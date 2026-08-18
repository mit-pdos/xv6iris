(* WpSconfAlu.v -- the SIE-AGNOSTIC ALU leaf layer (interrupt-sweep
   stage 5, first family file): the [sconf]+[sie_cap] twins of
   WpSmodePtAlu.v's leaves, over the agnostic gpr-write engines
   [wp_gpr_write_s_sconf] (WpSmodeIntr.v).

   Uniform transform vs the `_pt` originals:
     - resources: everything is bundled into `sie_cap_gpr m n b`
       (= hart_state ∗ sconf ∗ sie_cap m n b ∗ gpr_file (tp_pin m), with
       the kernel translation slot hidden inside sie_cap as strans_inv --
       no root_ppn binder, no separate tlb_inv_pt premise, and no ghost
       argument: the SIE ghost is the hart's canonical [sie_gname]);
     - the raw-cell/_scfg PAIR collapses to ONE lemma (sconf is the
       only bundle; raw-cell forms stay in WpSmodePtAlu for the mycpu
       fraction-island until the sweep completes);
     - NEW premise `rd_ok rd` on every rd-writing leaf: [sie_cap] is
       keyed on sp ([sie_cap_retarget]) and the register file PINS tp
       (HartTp.v), so a generic write may target neither.  The sp-MOVING
       instructions (c.addi sp, imm / c.addi16sp) live at the END of this
       file -- a generic transformer engine plus the direct PUSH/POP specs
       (wp_caddi{_sp,16sp}_{push,pop}_s_sconf) that trade the moved
       slots against [sie_cap]'s available count;
     - a register read at a VARIABLE index is [rget m rs] (HartTp.v),
       which is correct at tp too; a read of a CONCRETE register (sp, x0)
       stays the plain map lookup -- [rget] reduces to it by conversion.
       A leaf that reads a register the CALLER chooses states
       `ops_ok b rd rs1 rs2` (IntrDefs.v) IN the `rd_ok` slot instead of
       `rd_ok rd`: [rget] is a lookup in [tp_pin m] and so depends on the
       ambient hart at exactly tp, which will matter once the funnel's
       σ-callback moves inside [wp_next] (see IntrDefs.src_ok -- the premise
       is deliberately landed ahead of its consumer, DO NOT DROP IT).  The
       leaves whose engine operands are [rd] itself or a concrete register
       read nothing a caller varies, so they keep plain `rd_ok rd` and build
       the engine's premise with [ops_ok_self] / [ops_ok_conc];
     - every continuation is wrapped in [wp_next b]: with interrupts
       enabled the instruction can be trapped and the thread resumed on a
       DIFFERENT hart, and the rebound [CID] binder makes every resource
       inside the lambda about THAT hart;
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
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase WpMmodeShiftiop WpMmodeMul ExecCommon StackOwn.
Require Import SmodeCore.
Require Import RiscvExtras.
Require Import IntrDefs WpSmodeIntr.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.
Import Defs.

Section WpSconfAlu.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context {kt : ktier}.
  (* the value of [cpus[cid].proc]: a THREAD invariant, threaded through the
     bundle like the register map.  Implicit, so no call site changes. *)
  Context {p : mword 64}.

  (* ---- ITYPE family ---------------------------------------------------- *)

  (* addi rd, rs1, imm (base width) is [wp_addi_s_sconf] (WpSmodeIntr.v). *)

  Lemma wp_caddi4spn_s_sconf
      (pc : mword 64) (rdc : cregidx) (nzimm : mword 8) (rd : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    creg2reg_idx rdc = Regidx rd ->
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrdc Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    (* c.addi4spn reads sp, a CONCRETE register, so the engine's source guard
       is derived here and this leaf keeps its plain [rd_ok rd] premise. *)
    pose proof (ops_ok_conc b rd csp_rs1 csp_rs1 Hrdok
                  ltac:(rdok_tpne) ltac:(rdok_tpne)) as Hops.
    unshelve iApply (wp_gpr_write_s_sconf pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval := add_vec (rget m rd) (sign_extend' 64 (sign_extend' 12 imm)) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_candi_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval := and_vec (rget m rd) (sign_extend' 64 (sign_extend' 12 imm)) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ANDI_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_andi_val. rewrite Hva. reflexivity.
  Qed.

  (* c.li rd, imm is [wp_cli_s_sconf] (WpSmodeIntr.v). *)

  Lemma wp_sltiu_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (rget m rs1) (sign_extend' 64 imm))) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sltiu_val. rewrite Hva Hwval. reflexivity.
  Qed.

  (* ---- RTYPE family ---------------------------------------------------- *)

  Lemma wp_cadd_s_sconf
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let wval := add_vec (rget m rd) (rget m rs2) in
    uint rd <> 0 ->
    ops_ok b rd rd rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rd) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rd rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val. rewrite Hva Hvb. reflexivity.
  Qed.

  Lemma wp_cmv_s_sconf
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let wval := add_vec zero_reg (rget m rs2) in
    uint rd <> 0 ->
    ops_ok b rd rs2 rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      change (execute (RTYPE (Regidx rs2, Regidx (zero_extend' 5 ('b"00") : mword 5), Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx (zero_extend' 5 ('b"00") : mword 5)) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 (zero_extend' 5 ('b"00") : mword 5) rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true by (vm_compute; reflexivity).
      rewrite Hva. reflexivity.
  Qed.

  Lemma wp_sltu_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    zero_extend' 64 (bool_to_bit (zopz0zI_u (rget m rs1) (rget m rs2))) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_sltu_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_cor_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    or_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* c.and rd,rd,rs2 (register-register AND; the freerange PGROUNDUP mask
     step -- homed here since it is an ordinary c.and leaf like [wp_cor_s_sconf]
     above, not freerange-specific). *)
  Lemma wp_cand_s_sconf
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let wval := and_vec (rget m rd) (rget m rs2) in
    uint rd <> 0 ->
    ops_ok b rd rd rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rd rd s_pc Hrd).
      unfold gpr_and_val. rewrite Hva Hvb. reflexivity.
  Qed.

  (* the base (4-byte) [and rd,rs1,rs2] with rd <> rs1, which the compressed
     [wp_cand_s_sconf] above cannot express: vmfault's [and s4,s2,a5] and both
     copy loops' PGROUNDDOWN mask a virtual address with -4096 into a
     DIFFERENT register. *)
  Lemma wp_and_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    and_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_and_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* the BASE (4-byte) [addiw rd,rs1,imm], with rd and rs1 distinct -- the
     compressed [wp_caddiw_s_sconf] above only covers [c.addiw rd,rd,imm].
     [sext.w rd,rs1] is this instruction at imm = 0, which is how both copy
     loops narrow the chunk length to 32 bits for memmove. *)
  Lemma wp_addiw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64 (subrange_vec_dec (add_vec (rget m rs1) (sign_extend' 64 imm)) 31 0) in
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ADDIW (imm, Regidx rs1, Regidx rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ADDIW (imm, Regidx rs1, Regidx rd))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ADDIW_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addiw_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_sub_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sub_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
      rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* the COMPRESSED [c.sub] -- same leaf, 2-byte pc bump.  (The
     [C_SUB -> RTYPE] expansion is [WpMmodeLeafBase.exec_execute_C_SUB].)
     Stated with the stored value as an explicit [wval] so the term the map
     holds is CLOSED -- the "stored value containing an insert-lookup"
     derailment in claude-notes/durable-notes.md.  [wp_csub_s_sconf] below is
     the encoding's own shape (c.sub can only encode rd = rs1) as a
     restatement of this one. *)
  Lemma wp_csub_wval_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sub_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) SUB).
      rewrite (exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_sub_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* the shape the C.SUB encoding actually has, at the stored value inline. *)
  Lemma wp_csub_s_sconf
      (pc : mword 64) (rd rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let wval := sub_vec (rget m rd) (rget m rs2) in
    uint rd <> 0 ->
    ops_ok b rd rd rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPE (Regidx rs2, Regidx rd, Regidx rd, SUB)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    intros Hrd Hops.
    exact (wp_csub_wval_s_sconf pc rd rd rs2
             (sub_vec (rget m rd) (rget m rs2)) m n b
             Hrd Hops eq_refl).
  Qed.

  Lemma wp_csubw_wval_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sign_extend' 64
      (sub_vec (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
               (subrange_vec_dec (rget m rs2) 31 0 : mword 32)) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)))
        with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) SUBW).
      rewrite (exec_execute_RTYPEW_SUBW_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_subw_val, gpr_src. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_csubw_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5)
      (m : regfile) (n : nat) (b : bool) :
    let wval := sign_extend' 64 (sub_vec (subrange_vec_dec (rget m rs1) 31 0 : mword 32) (subrange_vec_dec (rget m rs2) 31 0 : mword 32)) in
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval Hrd Hops.
    exact (wp_csubw_wval_s_sconf pc rd rs1 rs2
             (sign_extend' 64 (sub_vec (subrange_vec_dec (rget m rs1) 31 0 : mword 32) (subrange_vec_dec (rget m rs2) 31 0 : mword 32))) m n b
             Hrd Hops eq_refl).
  Qed.

  Lemma wp_add_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    add_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      change (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)))
        with (execute_RTYPE (Regidx rs2) (Regidx rs1) (Regidx rd) ADD).
      rewrite (exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_rd_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* ---- UTYPE / ADDIW / SHIFTIOP families ------------------------------- *)

  (* base (32-bit) SLLI: [slli rd,rs1,shamt] with rd <> rs1 (not compressible). *)
  Lemma wp_slli_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    shift_bits_left (rget m rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_clui_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    luival imm = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (UTYPE (imm, Regidx rd, LUI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI)) wval m n b
              Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc _ _.
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hwval. reflexivity.
  Qed.

  (* base (4-byte) LUI: same value function as [wp_clui_s_sconf], 4-byte pc bump. *)
  Lemma wp_lui_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 20) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    luival imm = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (UTYPE (imm, Regidx rd, LUI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI)) wval m n b
              Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc _ _.
      rewrite (exec_execute_UTYPE_LUI_gpr rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      rewrite Hwval. reflexivity.
  Qed.

  (* SLLIW: shift the source's low 32 bits by a 5-bit shamt, sign-extend back. *)
  Lemma wp_slliw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sign_extend' 64 (shift_bits_left (subrange_vec_dec (rget m rs1) 31 0 : mword 32) shamt) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIWOP_SLLIW_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slliw_val, gpr_src. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_caddiw_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64 (subrange_vec_dec (add_vec (rget m rd) (sign_extend' 64 (sign_extend' 12 imm))) 31 0) in
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ADDIW_gpr rd rd (sign_extend' 12 imm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addiw_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_cslli_s_sconf
      (pc : mword 64) (rsd : regidx) (rd : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval :=
      shift_bits_left (rget m rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) in
    rsd = Regidx rd ->
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrsd Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_csrli_s_sconf
      (pc : mword 64) (crsd : cregidx) (rd : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval :=
      shift_bits_right (rget m rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) in
    creg2reg_idx crsd = Regidx rd ->
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hcrsd Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_srli4_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 6)
      (m : regfile) (n : nat) (b : bool) :
    let wval :=
      shift_bits_right (rget m rs1) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) in
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.


  (* base-width addi (rd != x0, rd != sp): [wval] is the model's
     [gpr_addi_val] at map-form operands. *)
  Lemma wp_addi4_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12)
      (m : regfile) (n : nat) (b : bool) :
    let wval := add_vec (rget m rs1) (sign_extend' 64 imm) in
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ADDI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  (* li rd,imm -- the 4-byte [addi rd,x0,imm] the assembler emits for an
     immediate too wide for [c.li].  The base-encoding analogue of
     [wp_cli_s_sconf] (WpSmodeIntr.v): rs1 is x0, so NO register is read and the
     written value is the sign-extended immediate outright -- which is why this
     cannot be an instance of [wp_addi4_s_sconf], whose post would read
     [m !!! Regidx zreg]. *)
  Lemma wp_li4_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    add_vec zero_reg (sign_extend' 64 imm) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, zreg, Regidx rd, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok Hwval) "Hcg Hpc Hinstr Hcont".
    (* li reads x0 and nothing else -- the reason this cannot be an instance of
       [wp_addi4_s_sconf] is the same reason it needs no source premise. *)
    pose proof (ops_ok_conc b rd (zero_extend' 5 ('b"00"))
                  (zero_extend' 5 ('b"00")) Hrdok
                  ltac:(rdok_tpne) ltac:(rdok_tpne)) as Hops.
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (imm, zreg, Regidx rd, ADDI)) wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.



  (* ------------------------------------------------------------------- *)
  (* The PC-READING 4-byte gpr-write engine (auipc): the base engine      *)
  (* with [register_lookup PC s_pc = pc] handed to the exec hypothesis.   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_gpr_write_s_sconf_base_pc
      (pc : mword 64) (rd rsa rsb : mword 5) (i : instruction) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rsa rsb ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4 ->
       register_lookup PC s_pc.(sregs) = pc ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = rget m rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = rget m rsb ->
       exec (execute i) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false i -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hbexec) "Hcg Hpc Hinstr Hcont".
    ops_ok_split Hops.
    iApply (wp_instr_s_sconf m n b pc false i with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    (* the two source reads cross the rebinding: the file the callback delivered
       is the REBOUND hart's pin, while [Hbexec] is stated at the entry hart's
       [rget m rs].  [ops_ok] says neither source is tp, so the words agree. *)
    destruct (rget_next_ops_indep (CID := CID0) b p CID m rd rsa rsb Hs Hops)
      as [Hra Hrb].
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    assert (LpcS : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc; rewrite ?sregs_set_reg.
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (CID := CID) rsa (tp_pin (CID := CID) m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value (CID := CID) rsb (tp_pin (CID := CID) m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc (tp_pin (CID := CID) m) (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz (CID := CID) rd _ Hrd).
    iMod (reg_update (CID := CID) _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz (CID := CID) rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 LpcS (eq_trans Lva0 Hra) (eq_trans Lvb0 Hrb)). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 4)
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    assert (Hsp : m !!! Regidx csp_rs1
                  = <[Regidx rd := regval_into_reg wval]> m !!! Regidx csp_rs1)
      by (symmetry; apply upd_ne; congruence).
    (* the leaf's own write commutes with the tp pin *)
    tp_refold (rd_ok_tp _ (ops_ok_rd _ _ _ _ Hops)) "Hfile".
    iDestruct (sie_cap_retarget (CID := CID) m
                 (<[Regidx rd := regval_into_reg wval]> m) n b Hsp with "Hcap") as "Hcap".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
       obligation is discharged by instantiating it here. *)
    iApply ("Hcont" $! CID with "[] Hcg [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
  Qed.

  Lemma wp_auipc_s_sconf
      (pc : mword 64) (rd : mword 5) (imm : mword 20)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (UTYPE (imm, Regidx rd, AUIPC)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg (add_vec pc (auipc_off imm))]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base_pc pc rd rd rd
              (UTYPE (imm, Regidx rd, AUIPC))
              (add_vec pc (auipc_off imm)) m n b
              Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    intros s_pc Hnpc HPCpc _ _.
    rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite HPCpc. reflexivity.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* SP-MOVERS: the cap engine takes a caller-supplied [sie_cap]          *)
  (* TRANSFORMER (n -> n') instead of the rd <> sp half of [rd_ok] --     *)
  (* an sp-write trades slots against the available count where the       *)
  (* function proof does its stack bookkeeping.  The push/pop leaves      *)
  (* below instantiate it with [sie_cap_push]/[sie_cap_pop].              *)
  (* The tp half of [rd_ok] does NOT go away, though: the bundle owns     *)
  (* [gpr_file (tp_pin m)] (HartTp.v), so even an sp-mover may not write  *)
  (* tp -- and this engine READS [rget m rsa] / [rget m rsb] like the     *)
  (* others, so it needs the same source guard.  Both facts ride in       *)
  (* [ops_ok_sp b rd rsa rsb] (IntrDefs.v), which is [ops_ok] with the sp *)
  (* conjunct dropped and the identical [src_ok] read side kept; its rd   *)
  (* half is what [tp_refold] needs to restate the engine's output write  *)
  (* as a write under the pin.  (Both call sites below are at rd = sp and *)
  (* read sp, so [ltac:(rdok)] closes the whole thing.)                   *)
  (* ------------------------------------------------------------------- *)
  (* THE ENCODING WIDTH IS A PARAMETER, because kexec's frame does not fit a
     compressed sp-move.  [c.addi sp]/[c.addi16sp] reach -512..+496, and kexec
     pushes 544 bytes, so gcc emits a BASE-encoded [addi sp,sp,-544] /
     [addi sp,sp,544] -- the only function in the tree that does.  The funnel
     underneath ([wp_instr_s_sconf]) is already width-generic, so this is the
     one engine at both widths and [wp_gpr_write_s_sconf_cap] below is its
     instance at [c := true]; the base-width sp movers are at the end of the
     push/pop group. *)
  Lemma wp_gpr_write_s_sconf_cap_w
      (pc : mword 64) (c : bool) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc (if c then 2 else 4) ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = rget m rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = rget m rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc c base -∗
    (* THE TRANSFORMER IS HART-GENERIC, and it has to be: the capability it
       rewrites is the one the σ-callback delivers, i.e. the REBOUND hart's,
       while the caller writes this wand down at its own.  [sie_cap] is
       per-hart (it owns the SIE arm), so nothing transports it -- but every
       proof of a transformer is uniform in the hart, so quantifying costs the
       builders one [iIntros (CIDx)]. *)
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc (if c then 2 else 4)) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hbexec) "Hcg Hpc Hinstr Hrecap Hcont".
    pose proof (ops_ok_sp_rd _ _ _ _ Hops) as Hrdtp.
    iApply (wp_instr_s_sconf m n b pc c base with "Hcg Hpc Hinstr").
    (* FREE THE NAME [CID] FOR THE REBOUND HART.  A section variable is an
       ordinary context entry inside a proof, so [rename] moves it aside --
       and the STATEMENT never sees that, so the 184 call sites that name this
       tier's harts as [(CID := ...)] keep working.  Introducing the new hart
       under a different name instead would force a [(CID := ...)] annotation on
       every hart-indexed term the body writes out ([tp_pin m], [rget m rs]);
       with the rename the body below is UNCHANGED. *)
    rename CID into CID0.
    iIntros (CID Hs σ Hpceq) "Hsc Hcap Hfile Hnpc [Hreg Hmem]".
    (* the two source reads cross the rebinding: the file the callback delivered
       is the REBOUND hart's pin, while [Hbexec] is stated at the entry hart's
       [rget m rs].  [ops_ok] says neither source is tp, so the words agree. *)
    (* [ops_ok_sp] here, not [ops_ok] -- the cap engine lets rd BE sp -- so the
       two sources come out one at a time. *)
    pose proof (rget_next_indep (CID := CID0) b p CID m rsa Hs
                  (ops_ok_sp_s1 _ _ _ _ Hops)) as Hra.
    pose proof (rget_next_indep (CID := CID0) b p CID m rsb Hs
                  (ops_ok_sp_s2 _ _ _ _ Hops)) as Hrb.
    iMod (reg_update (CID := CID) _ nextPC _ (add_vec_int pc (if c then 2 else 4)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc (if c then 2 else 4))).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc (if c then 2 else 4))
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rsa) with "Hfile") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value (CID := CID) rsa (tp_pin (CID := CID) m (Regidx rsa)) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfile".
    iDestruct (gpr_file_lookup_acc (tp_pin (CID := CID) m) (Regidx rsb) with "Hfile") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value (CID := CID) rsb (tp_pin (CID := CID) m (Regidx rsb)) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfile".
    iDestruct (gpr_file_insert_acc (tp_pin (CID := CID) m) (Regidx rd) (regval_into_reg wval) with "Hfile") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz (CID := CID) rd _ Hrd).
    iMod (reg_update (CID := CID) _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" with "[Hrdc]") as "Hfile".
    { rewrite (gpr_pt_nz (CID := CID) rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 (eq_trans Lva0 Hra) (eq_trans Lvb0 Hrb)). }
    iSplitL "Hreg Hmem".
    { unfold s_pc; rewrite ?sregs_set_reg ?mem_set_reg. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc (if c then 2 else 4))
      by (tmig; exact Lnpc0).
    iEval (rewrite Lnpc) in "Hpc'".
    (* the leaf's own write commutes with the tp pin *)
    tp_refold Hrdtp "Hfile".
    iDestruct ("Hrecap" $! CID with "Hcap") as "[Hcap HP]".
    iDestruct (sie_cap_gpr_join (CID := CID) with "Hhs' Hsc Hcap Hfile") as "Hcg".
    (* STAGE 1: the engine resumes on the SAME hart, so the step's [wp_next]
       obligation is discharged by instantiating it here. *)
    iApply ("Hcont" $! CID with "[] Hcg HP [$Hpc' $Hnpc]").
    iPureIntro. exact Hs.
  Qed.

  (* the COMPRESSED cap engine, the shape every existing sp-mover is built
     over: the general one at [c := true]. *)
  Lemma wp_gpr_write_s_sconf_cap
      (pc : mword 64) (rd rsa rsb : mword 5) (base : instruction) (wval : mword 64)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    uint rd <> 0 ->
    ops_ok_sp b rd rsa rsb ->
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = rget m rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = rget m rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true base -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx rd := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof. exact (wp_gpr_write_s_sconf_cap_w pc true rd rsa rsb base wval m n n' P b). Qed.

  (* the two real sp-movers over the cap engine: c.addi sp, imm and
     c.addi16sp.  The caller supplies the capability transformer -- at
     [b = false] the SIE arm is m-blind, so only the stack carve moves;
     at [b = true] it re-carves the >= 32-slot stack bound at the new sp,
     exactly where function proofs already do their stack bookkeeping.
     The moved value is [let]-bound OUTSIDE the [wp_next] lambda: it is a
     word read off the ENTRY map, at the hart we came from. *)
  Lemma wp_caddi_sp_s_sconf
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    let wval := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm)) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros "Hcg Hpc Hinstr Hrecap Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_cap pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) wval m n n' P b
              ltac:(vm_compute; discriminate)
              ltac:(rdok) _
              with "Hcg Hpc Hinstr Hrecap Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint (csp_rs1 : mword 5)) 0) with false by (vm_compute; reflexivity).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_caddi16sp_s_sconf
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    let wval := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros "Hcg Hpc Hinstr Hrecap Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_cap pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) wval m n n' P b
              ltac:(vm_compute; discriminate)
              ltac:(rdok) _
              with "Hcg Hpc Hinstr Hrecap Hcont").
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
  Lemma wp_caddi_sp_push_s_sconf
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm)) in
    (k <= n)%nat ->
    wval = pa_stk sp0 k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n - k) b p -∗
      stack_own (KTR := kt) sp0 k -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hk Hw) "Hcg Hpc Hinstr Hcont".
    assert (Hsp' : <[Regidx csp_rs1 := regval_into_reg wval]> m !!! Regidx csp_rs1
                   = pa_stk (m !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi_sp_s_sconf pc imm m n (n - k) (stack_own (KTR := kt) sp0 k) b
              with "Hcg Hpc Hinstr [] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iDestruct (sie_cap_push (CID := CIDx) m _ n k b Hk Hsp' with "Hcap")
        as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hframe Hpc").
    iPureIntro. exact Hs1.
  Qed.

  Lemma wp_caddi_sp_pop_s_sconf
      (pc : mword 64) (imm : mword 6)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (sign_extend' 12 imm)) in
    sp0 = pa_stk wval k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    stack_own (KTR := kt) wval k -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n + k) b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hw) "Hcg Hpc Hinstr Hframe Hcont".
    assert (Hsp : m !!! Regidx csp_rs1
                  = pa_stk (<[Regidx csp_rs1 := regval_into_reg wval]> m
                            !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi_sp_s_sconf pc imm m n (n + k) emp%I b
              with "Hcg Hpc Hinstr [Hframe] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iSplitL; [| done].
      iApply (sie_cap_pop (CID := CIDx) m _ n k b Hsp with "[Hframe] Hcap").
      rewrite upd_eq. iExact "Hframe". }
    iIntros (CID1 Hs1) "Hcg _ Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.

  Lemma wp_caddi16sp_push_s_sconf
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (caddi16sp_imm imm6)) in
    (k <= n)%nat ->
    wval = pa_stk sp0 k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n - k) b p -∗
      stack_own (KTR := kt) sp0 k -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hk Hw) "Hcg Hpc Hinstr Hcont".
    assert (Hsp' : <[Regidx csp_rs1 := regval_into_reg wval]> m !!! Regidx csp_rs1
                   = pa_stk (m !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi16sp_s_sconf pc imm6 m n (n - k) (stack_own (KTR := kt) sp0 k) b
              with "Hcg Hpc Hinstr [] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iDestruct (sie_cap_push (CID := CIDx) m _ n k b Hk Hsp' with "Hcap")
        as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hframe Hpc").
    iPureIntro. exact Hs1.
  Qed.

  Lemma wp_caddi16sp_pop_s_sconf
      (pc : mword 64) (imm6 : mword 6)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 (caddi16sp_imm imm6)) in
    sp0 = pa_stk wval k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc true (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)) -∗
    stack_own (KTR := kt) wval k -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n + k) b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hw) "Hcg Hpc Hinstr Hframe Hcont".
    assert (Hsp : m !!! Regidx csp_rs1
                  = pa_stk (<[Regidx csp_rs1 := regval_into_reg wval]> m
                            !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_caddi16sp_s_sconf pc imm6 m n (n + k) emp%I b
              with "Hcg Hpc Hinstr [Hframe] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iSplitL; [| done].
      iApply (sie_cap_pop (CID := CIDx) m _ n k b Hsp with "[Hframe] Hcap").
      rewrite upd_eq. iExact "Hframe". }
    iIntros (CID1 Hs1) "Hcg _ Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.


  (* ------------------------------------------------------------------- *)
  (* THE BASE-ENCODED sp MOVER: [addi sp,sp,imm12], the 4-byte form the     *)
  (* assembler falls back to when the frame is too large for c.addi16sp     *)
  (* (kexec's 544 bytes -- the tree's one such frame).  Same three lemmas   *)
  (* as the compressed family, over the width-generic cap engine.          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_addi_sp4_s_sconf
      (pc : mword 64) (imm : mword 12)
      (m : regfile) (n n' : nat) (P : iProp Σ) (b : bool) :
    let wval := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    ( ∀ CIDx : CpuId,
      sie_cap kt (CID := CIDx) m n b p -∗
      sie_cap kt (CID := CIDx) (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p ∗ P ) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) n' b p -∗
      P -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros "Hcg Hpc Hinstr Hrecap Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_cap_w pc false csp_rs1 csp_rs1 csp_rs1
              (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) wval m n n' P b
              ltac:(vm_compute; discriminate)
              ltac:(rdok) _
              with "Hcg Hpc Hinstr Hrecap Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 imm s_pc).
    replace (Z.eqb (uint (csp_rs1 : mword 5)) 0) with false by (vm_compute; reflexivity).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_addi_sp_push4_s_sconf
      (pc : mword 64) (imm : mword 12)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 imm) in
    (k <= n)%nat ->
    wval = pa_stk sp0 k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n - k) b p -∗
      stack_own (KTR := kt) sp0 k -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hk Hw) "Hcg Hpc Hinstr Hcont".
    assert (Hsp' : <[Regidx csp_rs1 := regval_into_reg wval]> m !!! Regidx csp_rs1
                   = pa_stk (m !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_addi_sp4_s_sconf pc imm m n (n - k) (stack_own (KTR := kt) sp0 k) b
              with "Hcg Hpc Hinstr [] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iDestruct (sie_cap_push (CID := CIDx) m _ n k b Hk Hsp' with "Hcap")
        as "[Hcap Hframe]".
      iFrame "Hcap Hframe". }
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hframe Hpc").
    iPureIntro. exact Hs1.
  Qed.

  Lemma wp_addi_sp_pop4_s_sconf
      (pc : mword 64) (imm : mword 12)
      (m : regfile) (n k : nat) (b : bool) :
    let sp0 := m !!! Regidx csp_rs1 in
    let wval := add_vec sp0 (sign_extend' 64 imm) in
    sp0 = pa_stk wval k ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗
    instr pc false (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)) -∗
    stack_own (KTR := kt) wval k -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx csp_rs1 := regval_into_reg wval]> m) (n + k) b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros sp0 wval.
    iIntros (Hw) "Hcg Hpc Hinstr Hframe Hcont".
    assert (Hsp : m !!! Regidx csp_rs1
                  = pa_stk (<[Regidx csp_rs1 := regval_into_reg wval]> m
                            !!! Regidx csp_rs1) k).
    { rewrite upd_eq. exact Hw. }
    iApply (wp_addi_sp4_s_sconf pc imm m n (n + k) emp%I b
              with "Hcg Hpc Hinstr [Hframe] [Hcont]").
    { iIntros (CIDx) "Hcap".
      iSplitL; [| done].
      iApply (sie_cap_pop (CID := CIDx) m _ n k b Hsp with "[Hframe] Hcap").
      rewrite upd_eq. iExact "Hframe". }
    iIntros (CID1 Hs1) "Hcg _ Hpc".
    iApply ("Hcont" $! CID1 with "[] Hcg Hpc").
    iPureIntro. exact Hs1.
  Qed.


  (* srl/ori/andi -- moved here from ProofWalk.v (leaves belong in the leaf file). *)
  Lemma wp_srl_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    shift_bits_right (rget m rs1)
      (subrange_vec_dec (rget m rs2) (Z.sub log2_xlen 1) 0) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPE_SRL_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_srl_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_ori_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs1 ->
    or_vec (rget m rs1) (sign_extend' 64 imm) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ORI)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ORI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_ori_val. rewrite Hva Hwval. reflexivity.
  Qed.

  (* [xori rd,rs1,imm].  copyinstr flips its [got_null] flag with
     [xori a5,a5,1] on its way to the return value. *)
  Lemma wp_xori_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs1 ->
    xor_vec (rget m rs1) (sign_extend' 64 imm) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_XORI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_xori_val. rewrite Hva Hwval. reflexivity.
  Qed.

  Lemma wp_andi_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (imm : mword 12) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs1 ->
    and_vec (rget m rs1) (sign_extend' 64 imm) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_ITYPE_ANDI_gpr rs1 rd imm s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_andi_val. rewrite Hva Hwval. reflexivity.
  Qed.


  (* base-width OR -- moved here from ProofMappages.v (dedup: leaf belongs in the leaf file). *)
  Lemma wp_or_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    or_vec (rget m rs1) (rget m rs2) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR)) wval m n b
              Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    intros s_pc Hnpc Hva Hvb.
    rewrite (exec_execute_RTYPE_OR_gpr rs2 rs1 rd s_pc Hrd).
    unfold gpr_or_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.


  (* ---- SRAI / MUL / ADDW ----
     Lifted out of ProofProcMapstacks, which needed them for its KSTACK(i)
     computation and had nowhere shared to put them.  procinit computes the
     same address, so these are now two-user leaves; the exec bridges they
     rest on are in WpMmodeLeafBase beside the others. *)

  Lemma wp_srai_s_sconf
      (pc : mword 64) (rd : mword 5) (shamt : mword 6) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      shift_bits_right_arith (rget m rd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) in
    uint rd <> 0 -> rd_ok rd ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hrdok) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI))
              wval
              m n b Hrd (ops_ok_self b rd Hrdok) _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRAI_gpr rd rd shamt s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srai_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  Lemma wp_mul_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64) (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2))
      (rget m rs1) (rget m rs2) (mulop_mul.(mul_op_result_part)) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul)) wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_MUL_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_mul_val. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  (* divu / remu rd,rs1,rs2 -- printint's [x /= base] and [x % base].  Both
     take the value as a caller-supplied [wval] (the model's own Z-level
     quotient/remainder at the map-form operands), so a call site that knows
     its divisor is nonzero closes the [Z.eqb .. 0] test by [vm_compute]
     instead of carrying the architectural divide-by-zero case around. *)
  Lemma wp_divu_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64) (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    to_bits_truncate 64
      (if Z.eqb (uint (rget m rs2)) 0 then (-1)%Z
       else Z.quot (uint (rget m rs1)) (uint (rget m rs2))) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_DIVU_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_divu_val, gpr_uint_src. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_remu_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64) (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    to_bits_truncate 64
      (if Z.eqb (uint (rget m rs2)) 0 then uint (rget m rs1)
       else Z.rem (uint (rget m rs1)) (uint (rget m rs2))) = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_REMU_gpr rs2 rs1 rd s_pc Hrd).
      unfold gpr_remu_val, gpr_uint_src. rewrite Hva Hvb Hwval. reflexivity.
  Qed.

  Lemma wp_addw_s_sconf
      (pc : mword 64) (rd rs2 : mword 5) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64 (add_vec (subrange_vec_dec (rget m rd) 31 0 : mword 32) (subrange_vec_dec (rget m rs2) 31 0 : mword 32)) in
    uint rd <> 0 -> ops_ok b rd rd rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc true (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 2) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf pc rd rd rs2
              (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_ADDW_gpr rs2 rd rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addw_val, gpr_src. rewrite Hva Hvb. reflexivity.
  Qed.

  (* subw rd,rs1,rs2 -- the 4-byte (base-encoding) 32-bit subtract whose
     result is sign-extended into rd.  Unlike [wp_addw_s_sconf] (the
     compressed 2-operand [c.addw]) the three registers are independent. *)
  Lemma wp_subw_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64 (sub_vec (subrange_vec_dec (rget m rs1) 31 0 : mword 32) (subrange_vec_dec (rget m rs2) 31 0 : mword 32)) in
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))
              wval
              m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_SUBW_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_subw_val, gpr_src. rewrite Hva Hvb. reflexivity.
  Qed.

  (* addw rd,rs1,rs2 -- the 4-byte (base-encoding) 32-bit add whose result
     is sign-extended into rd.  Unlike [wp_addw_s_sconf] (the compressed
     two-operand [c.addw], rd = rs1) the three registers are independent;
     this is the ADDW twin of [wp_subw_s_sconf]. *)
  Lemma wp_addw4_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64 (add_vec (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
                               (subrange_vec_dec (rget m rs2) 31 0 : mword 32)) in
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval.
    iIntros (Hrd Hops) "Hcg Hpc Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_sconf_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))
              wval m n b Hrd Hops _
              with "Hcg Hpc Hinstr Hcont").
    - intros s_pc Hnpc Hva Hvb.
      rewrite (exec_execute_RTYPEW_ADDW_gpr rs2 rs1 rd s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addw_val, gpr_src. rewrite Hva Hvb. reflexivity.
  Qed.
End WpSconfAlu.

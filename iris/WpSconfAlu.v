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

   PER-NODE PORT: every leaf below now discharges an [swp (execute i)]
   OBLIGATION instead of an [exec] fact, through [WpSconfEngine.v]'s
   value-function engines ([wp_gpr_write_s_sconf_val{,_base,_w}], the
   sp-moving [_cap_val{,_w}] and the PC-lending [_pc_val_base]) -- the three
   engines that used to live in THIS file are those, generalized: an [exec]
   fact constrains the start state only, and a per-node walk may be
   interfered with between nodes.  A leaf's proof is one [iApply] of the
   engine plus one [iApply] of the matching [WpMmodeSwpBase] node shape;
   NO LEAF STATEMENT MOVED.

   ALSO HERE, folded in from the consumer files they were parked in (the
   per-node port is the build that can afford editing this one): the three
   W-width leaves [wp_srliw_s_sconf] (was WpSconfSrliw.v),
   [wp_sraiw_s_sconf] and [wp_sllw_s_sconf] / [wp_sllw_wval_s_sconf] (were
   ProofBallocParts.v / ProofBfree.v), with their exec bridges. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import gen_heap ghost_map ghost_var invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec.
Require Import RegFile HartTp WpNext WpGpr InstrBytes WpMmodeLeafBase WpMmodeShiftiop ExecCommon StackOwn.
Require Import RiscvExtras.
Require Import HartSwp WpMmodeSwpBase.
Require Import WpSconfEngine.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(*  THE THREE W-WIDTH EXEC BRIDGES that used to sit in consumer files.    *)
(*                                                                       *)
(*  [srliw] / [sraiw] are the other two branches of [execute_SHIFTIWOP]'s *)
(*  three-way match (WpMmodeShiftiop.v has the SLLIW one) and [sllw] is   *)
(*  the register-shift branch of [execute_RTYPEW]'s.  They were parked in *)
(*  WpSconfSrliw.v / ProofBallocParts.v / ProofBfree.v only because       *)
(*  editing this file used to be unaffordable; the per-node port pays for *)
(*  a full rebuild anyway, so they are home.  The WP leaves below no      *)
(*  longer consume them (a converted leaf discharges an [swp] obligation  *)
(*  at a WpMmodeSwpBase node shape), but they are the exec-side           *)
(*  statements of the same three instructions and belong beside the       *)
(*  rest of that catalogue.                                              *)
(* ===================================================================== *)

Lemma exec_execute_SHIFTIWOP_SRLIW (shamt : mword 5) (rs1 rd : regidx)
    (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64
          (shift_bits_right (subrange_vec_dec a 31 0 : mword 32) shamt)))
       s = Some (tt, s') ->
  exec (execute (SHIFTIWOP (shamt, rs1, rd, SRLIW))) s
  = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIWOP (shamt, rs1, rd, SRLIW)))
    with (execute_SHIFTIWOP shamt rs1 rd SRLIW).
  unfold execute_SHIFTIWOP. cbn match.
  rewrite (exec_bind_Some _ _ _ a s Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_srliw_val (rs1 : mword 5) (shamt : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64 (shift_bits_right (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32) shamt).

Lemma exec_execute_SHIFTIWOP_SRLIW_gpr (rs1 rd : mword 5) (shamt : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_srliw_val rs1 shamt s))).
Proof.
  unfold gpr_srliw_val, gpr_src.
  eapply exec_execute_SHIFTIWOP_SRLIW.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Lemma exec_execute_SHIFTIWOP_SRAIW (shamt : mword 5) (rs1 rd : regidx)
    (a : mword 64) s s' :
  exec (rX_bits rs1) s = Some (a, s) ->
  exec (wX_bits rd (sign_extend' 64
          (shift_bits_right_arith (subrange_vec_dec a 31 0 : mword 32) shamt)))
       s = Some (tt, s') ->
  exec (execute (SHIFTIWOP (shamt, rs1, rd, SRAIW))) s
  = Some (RETIRE_SUCCESS, s').
Proof.
  intros Ha Hw.
  change (execute (SHIFTIWOP (shamt, rs1, rd, SRAIW)))
    with (execute_SHIFTIWOP shamt rs1 rd SRAIW).
  unfold execute_SHIFTIWOP. cbn match.
  rewrite (exec_bind_Some _ _ _ a s Ha).
  rewrite (exec_bind0_Some _ _ _ _ _ Hw). apply exec_returnm.
Qed.

Definition gpr_sraiw_val (rs1 : mword 5) (shamt : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64
    (shift_bits_right_arith (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32) shamt).

Lemma exec_execute_SHIFTIWOP_SRAIW_gpr (rs1 rd : mword 5) (shamt : mword 5) s :
  exec (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sraiw_val rs1 shamt s))).
Proof.
  unfold gpr_sraiw_val, gpr_src.
  eapply exec_execute_SHIFTIWOP_SRAIW.
  - apply (exec_rX_bits_gpr rs1 s).
  - apply (exec_wX_bits_gpr rd _ s).
Qed.

Definition gpr_sllw_val (rs2 rs1 : mword 5) (s : mstate) : mword 64 :=
  sign_extend' 64
    (shift_bits_left (subrange_vec_dec (gpr_src rs1 s) 31 0 : mword 32)
       (subrange_vec_dec (subrange_vec_dec (gpr_src rs2 s) 31 0 : mword 32) 4 0)).

Lemma exec_execute_RTYPEW_SLLW_gpr (rs2 rs1 rd : mword 5) s :
  exec (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW))) s
  = Some (RETIRE_SUCCESS,
          if Z.eqb (uint rd) 0 then s
          else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                 (regval_into_reg (gpr_sllw_val rs2 rs1 s))).
Proof.
  unfold gpr_sllw_val, gpr_src.
  change (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)))
    with (execute_RTYPEW (Regidx rs2) (Regidx rs1) (Regidx rd) SLLW).
  unfold execute_RTYPEW. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  apply exec_returnm.
Qed.


Section WpSconfAlu.
  Context `{!riscvGS Σ}.
  Context `{!xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.
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
    (* the source is the CONCRETE sp, so the engine's [rget]-spelled value
       premise is this leaf's map-spelled one ([IntrDefs.tp_pin_sp]). *)
    assert (Hspv : add_vec (rget m csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm))
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
      by (by rewrite (rget_sp m)).
    iApply (wp_gpr_write_s_sconf_val pc rd csp_rs1 csp_rs1
              (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 (caddi4spn_imm nzimm)))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))
              m n b Hrd Hops Hspv
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) csp_rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))) RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 (caddi4spn_imm nzimm))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 (sign_extend' 12 imm))) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI))) RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 (sign_extend' 12 imm))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))
              (fun a _ => and_vec a (sign_extend' 64 (sign_extend' 12 imm))) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ANDI))) RETIRE_SUCCESS
              (fun a => and_vec a (sign_extend' 64 (sign_extend' 12 imm))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU))
              (fun a _ => zero_extend' 64 (bool_to_bit (zopz0zI_u a (sign_extend' 64 imm)))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU))) RETIRE_SUCCESS
              (fun a => zero_extend' 64 (bool_to_bit (zopz0zI_u a (sign_extend' 64 imm)))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))
              (add_vec) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rd rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD))) RETIRE_SUCCESS
              (add_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rs2 rs2
              (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (fun a _ => add_vec zero_reg a) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iDestruct (gpr_file_x0 (CID := CIDn) (tp_pin (CID := CIDn) m)
                 (zero_extend' 5 ('b"00"))
                 ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    iApply (swp_mono (CID := CIDn) with "[] [Hf]");
      [| iApply (swp_execute_rrw (CID := CIDn) rs2 (zero_extend' 5 ('b"00")) rd
                   (tp_pin (CID := CIDn) m)
                   (execute (RTYPE (Regidx rs2,
                                    Regidx (zero_extend' 5 ('b"00") : mword 5),
                                    Regidx rd, ADD)))
                   RETIRE_SUCCESS add_vec eq_refl Hrd with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|]. rewrite Hx0. iExact "Hf".
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))
              (fun a c => zero_extend' 64 (bool_to_bit (zopz0zI_u a c))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))) RETIRE_SUCCESS
              (fun a c => zero_extend' 64 (bool_to_bit (zopz0zI_u a c))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))
              (or_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))) RETIRE_SUCCESS
              (or_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rs2
              (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))
              (and_vec) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rd rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))) RETIRE_SUCCESS
              (and_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))
              (and_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))) RETIRE_SUCCESS
              (and_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ADDIW (imm, Regidx rs1, Regidx rd))
              (fun a _ => sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0)) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw2 (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ADDIW (imm, Regidx rs1, Regidx rd))) RETIRE_SUCCESS
              (fun a => sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))
              (sub_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))) RETIRE_SUCCESS
              (sub_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))
              (sub_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))) RETIRE_SUCCESS
              (sub_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))
              (fun a c => sign_extend' 64 (sub_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))) RETIRE_SUCCESS
              (fun a c => sign_extend' 64 (sub_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))
              (add_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))) RETIRE_SUCCESS
              (add_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))
              (fun a _ => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))) RETIRE_SUCCESS
              (fun a => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI))
              (fun _ _ => luival imm) wval m n b Hrd (ops_ok_self b rd Hrdok) Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_pure_w (CID := CIDn) rd (tp_pin (CID := CIDn) m)
              (execute (UTYPE (imm, Regidx rd, LUI))) RETIRE_SUCCESS
              (luival imm) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rd rd
              (UTYPE (imm, Regidx rd, LUI))
              (fun _ _ => luival imm) wval m n b Hrd (ops_ok_self b rd Hrdok) Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_pure_w (CID := CIDn) rd (tp_pin (CID := CIDn) m)
              (execute (UTYPE (imm, Regidx rd, LUI))) RETIRE_SUCCESS
              (luival imm) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW))
              (fun a _ => sign_extend' 64 (shift_bits_left (subrange_vec_dec a 31 0 : mword 32) shamt)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw2 (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW))) RETIRE_SUCCESS
              (fun a => sign_extend' 64 (shift_bits_left (subrange_vec_dec a 31 0 : mword 32) shamt)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))
              (fun a _ => sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 (sign_extend' 12 imm))) 31 0)) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw2 (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd))) RETIRE_SUCCESS
              (fun a => sign_extend' 64 (subrange_vec_dec (add_vec a (sign_extend' 64 (sign_extend' 12 imm))) 31 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))
              (fun a _ => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))) RETIRE_SUCCESS
              (fun a => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))
              (fun a _ => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))) RETIRE_SUCCESS
              (fun a => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
              (fun a _ => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))) RETIRE_SUCCESS
              (fun a => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 imm)) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))) RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (imm, zreg, Regidx rd, ADDI))
              (fun _ _ => add_vec zero_reg (sign_extend' 64 imm))
              wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iDestruct (gpr_file_x0 (CID := CIDn) (tp_pin (CID := CIDn) m)
                 (zero_extend' 5 ('b"00"))
                 ltac:(vm_compute; reflexivity) with "Hf") as "[%Hx0 Hf]".
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    iApply (swp_mono (CID := CIDn) with "[] [Hf]");
      [| iApply (swp_execute_rw (CID := CIDn) (zero_extend' 5 ('b"00")) rd
                   (tp_pin (CID := CIDn) m)
                   (execute (ITYPE (imm,
                                    Regidx (zero_extend' 5 ('b"00") : mword 5),
                                    Regidx rd, ADDI)))
                   RETIRE_SUCCESS
                   (fun a => add_vec a (sign_extend' 64 imm))
                   eq_refl Hrd with "Hcert Hf") ].
    iIntros (e) "[-> Hf]". iSplitR; [done|]. rewrite Hx0. iExact "Hf".
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
    iApply (wp_gpr_write_s_sconf_pc_val_base pc rd rd rd
              (UTYPE (imm, Regidx rd, AUIPC))
              (fun _ _ => add_vec pc (auipc_off imm))
              (add_vec pc (auipc_off imm)) m n b Hrd
              (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf HPC".
    iApply (swp_execute_pcw (CID := CIDn) rd (tp_pin (CID := CIDn) m)
              (execute (UTYPE (imm, Regidx rd, AUIPC))) RETIRE_SUCCESS pc
              (fun w => add_vec w (auipc_off imm)) eq_refl Hrd
              with "Hcert Hf HPC").
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
    (* the source is the CONCRETE sp, so the engine's [rget]-spelled value
       premise is this leaf's map-spelled one ([IntrDefs.tp_pin_sp]). *)
    assert (Hspv : add_vec (rget m csp_rs1) (sign_extend' 64 (sign_extend' 12 imm))
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm)))
      by (by rewrite (rget_sp m)).
    iApply (wp_gpr_write_s_sconf_cap_val pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 (sign_extend' 12 imm)))
              wval m n n' P b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              Hspv
              with "[] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) csp_rs1 csp_rs1 (tp_pin (CID := CIDn) m)
              (execute (ITYPE (sign_extend' 12 imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)))
              RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 (sign_extend' 12 imm)))
              eq_refl ltac:(vm_compute; discriminate) with "Hcert Hf").
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
    (* the source is the CONCRETE sp, so the engine's [rget]-spelled value
       premise is this leaf's map-spelled one ([IntrDefs.tp_pin_sp]). *)
    assert (Hspv : add_vec (rget m csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6))
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))
      by (by rewrite (rget_sp m)).
    iApply (wp_gpr_write_s_sconf_cap_val pc csp_rs1 csp_rs1 csp_rs1
              (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 (caddi16sp_imm imm6)))
              wval m n n' P b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              Hspv
              with "[] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) csp_rs1 csp_rs1 (tp_pin (CID := CIDn) m)
              (execute (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI)))
              RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 (caddi16sp_imm imm6)))
              eq_refl ltac:(vm_compute; discriminate) with "Hcert Hf").
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
    (* the source is the CONCRETE sp, so the engine's [rget]-spelled value
       premise is this leaf's map-spelled one ([IntrDefs.tp_pin_sp]). *)
    assert (Hspv : add_vec (rget m csp_rs1) (sign_extend' 64 imm)
                   = add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm))
      by (by rewrite (rget_sp m)).
    iApply (wp_gpr_write_s_sconf_cap_val_w pc false csp_rs1 csp_rs1 csp_rs1
              (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI))
              (fun a _ => add_vec a (sign_extend' 64 imm))
              wval m n n' P b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              Hspv
              with "[] Hcg Hpc Hinstr Hrecap Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) csp_rs1 csp_rs1 (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)))
              RETIRE_SUCCESS
              (fun a => add_vec a (sign_extend' 64 imm))
              eq_refl ltac:(vm_compute; discriminate) with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL))
              (fun a c => shift_bits_right a (subrange_vec_dec c (Z.sub log2_xlen 1) 0)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SRL))) RETIRE_SUCCESS
              (fun a c => shift_bits_right a (subrange_vec_dec c (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ORI))
              (fun a _ => or_vec a (sign_extend' 64 imm)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx rs1, Regidx rd, ORI))) RETIRE_SUCCESS
              (fun a => or_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, XORI))
              (fun a _ => xor_vec a (sign_extend' 64 imm)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx rs1, Regidx rd, XORI))) RETIRE_SUCCESS
              (fun a => xor_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (ITYPE (imm, Regidx rs1, Regidx rd, ANDI))
              (fun a _ => and_vec a (sign_extend' 64 imm)) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (ITYPE (imm, Regidx rs1, Regidx rd, ANDI))) RETIRE_SUCCESS
              (fun a => and_vec a (sign_extend' 64 imm)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))
              (or_vec) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, OR))) RETIRE_SUCCESS
              (or_vec) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rd
              (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI))
              (fun a _ => shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) wval m n b Hrd (ops_ok_self b rd Hrdok) eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw (CID := CIDn) rd rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRAI))) RETIRE_SUCCESS
              (fun a => shift_bits_right_arith a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0)) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))
              (fun a c => mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2)) a c (mulop_mul.(mul_op_result_part))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (MUL (Regidx rs2, Regidx rs1, Regidx rd, mulop_mul))) RETIRE_SUCCESS
              (fun a c => mult_to_bits_half xlen (mulop_mul.(mul_op_signed_rs1)) (mulop_mul.(mul_op_signed_rs2)) a c (mulop_mul.(mul_op_result_part))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))
              (fun a c => to_bits_truncate 64 (if Z.eqb (uint c) 0 then (-1)%Z else Z.quot (uint a) (uint c))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))) RETIRE_SUCCESS
              (fun a c => to_bits_truncate 64 (if Z.eqb (uint c) 0 then (-1)%Z else Z.quot (uint a) (uint c))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (REM (Regidx rs2, Regidx rs1, Regidx rd, true))
              (fun a c => to_bits_truncate 64 (if Z.eqb (uint c) 0 then uint a else Z.rem (uint a) (uint c))) wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true))) RETIRE_SUCCESS
              (fun a c => to_bits_truncate 64 (if Z.eqb (uint c) 0 then uint a else Z.rem (uint a) (uint c))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val pc rd rd rs2
              (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW))
              (fun a c => sign_extend' 64 (add_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rd rd (tp_pin (CID := CIDn) m)
              (execute (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW))) RETIRE_SUCCESS
              (fun a c => sign_extend' 64 (add_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))
              (fun a c => sign_extend' 64 (sub_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))) RETIRE_SUCCESS
              (fun a c => sign_extend' 64 (sub_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) eq_refl Hrd with "Hcert Hf").
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
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))
              (fun a c => sign_extend' 64 (add_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) wval m n b Hrd Hops eq_refl
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))) RETIRE_SUCCESS
              (fun a c => sign_extend' 64 (add_vec (subrange_vec_dec a 31 0 : mword 32) (subrange_vec_dec c 31 0 : mword 32))) eq_refl Hrd with "Hcert Hf").
  Qed.
  (* ---- the three W-width leaves folded in from the consumer files ------ *)

  (* SRLIW: shift the source's low 32 bits RIGHT (logically) by a 5-bit
     shamt, sign-extend the 32-bit result back.  The [wp_slliw_s_sconf]
     twin, verbatim. *)
  Lemma wp_srliw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sign_extend' 64 (shift_bits_right (subrange_vec_dec (rget m rs1) 31 0 : mword 32) shamt)
      = wval ->
    sie_cap_gpr kt m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr kt (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    iApply (wp_gpr_write_s_sconf_val_base pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW))
              (fun a _ => sign_extend' 64
                 (shift_bits_right (subrange_vec_dec a 31 0 : mword 32) shamt))
              wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw2 (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRLIW)))
              RETIRE_SUCCESS
              (fun a => sign_extend' 64
                 (shift_bits_right (subrange_vec_dec a 31 0 : mword 32) shamt))
              eq_refl Hrd with "Hcert Hf").
  Qed.

  (* SRAIW: the same at an ARITHMETIC right shift -- balloc's signed
     divide of the C [int] [bi] by 8. *)
  Lemma wp_sraiw_s_sconf
      (pc : mword 64) (rd rs1 : mword 5) (shamt : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs1 ->
    sign_extend' 64
      (shift_bits_right_arith (subrange_vec_dec (rget m rs1) 31 0 : mword 32) shamt)
      = wval ->
    sie_cap_gpr KT1 m n b p -∗
    pc_is pc -∗ instr pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr KT1 (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    iApply (wp_gpr_write_s_sconf_val_base (kt := KT1) pc rd rs1 rs1
              (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW))
              (fun a _ => sign_extend' 64
                 (shift_bits_right_arith (subrange_vec_dec a 31 0 : mword 32) shamt))
              wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rw2 (CID := CIDn) rs1 rd (tp_pin (CID := CIDn) m)
              (execute (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SRAIW)))
              RETIRE_SUCCESS
              (fun a => sign_extend' 64
                 (shift_bits_right_arith (subrange_vec_dec a 31 0 : mword 32) shamt))
              eq_refl Hrd with "Hcert Hf").
  Qed.

  (* SLLW: shift the first source's low 32 bits LEFT by the second's low
     FIVE bits, sign-extending the 32-bit result back.  This is C's
     [(int)x << (y & 31)] and is how both allocators form the bit mask
     [1 << (bi % 8)].

     THE PAIR, as for [c.sub]: the two parked copies of this leaf were NOT
     the same statement -- bfree's took the stored value as an explicit
     [wval] (so the map it hands back holds a CLOSED term), balloc's spelled
     it inline.  Both are kept, the inline one as the [eq_refl] instance. *)
  Lemma wp_sllw_wval_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (wval : mword 64)
      (m : regfile) (n : nat) (b : bool) :
    uint rd <> 0 ->
    ops_ok b rd rs1 rs2 ->
    sign_extend' 64
      (shift_bits_left (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
         (subrange_vec_dec
            (subrange_vec_dec (rget m rs2) 31 0 : mword 32) 4 0)) = wval ->
    sie_cap_gpr KT1 m n b p -∗
    pc_is pc -∗
    instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr KT1 (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    iIntros (Hrd Hops Hwval) "Hcg Hpc Hinstr Hcont".
    iApply (wp_gpr_write_s_sconf_val_base (kt := KT1) pc rd rs1 rs2
              (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW))
              (fun a c => sign_extend' 64
                 (shift_bits_left (subrange_vec_dec a 31 0 : mword 32)
                    (subrange_vec_dec
                       (subrange_vec_dec c 31 0 : mword 32) 4 0)))
              wval m n b Hrd Hops Hwval
              with "[] Hcg Hpc Hinstr Hcont").
    iIntros (CIDn) "#Hcert Hf".
    iApply (swp_execute_rrw2 (CID := CIDn) rs2 rs1 rd (tp_pin (CID := CIDn) m)
              (execute (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)))
              RETIRE_SUCCESS
              (fun a c => sign_extend' 64
                 (shift_bits_left (subrange_vec_dec a 31 0 : mword 32)
                    (subrange_vec_dec
                       (subrange_vec_dec c 31 0 : mword 32) 4 0)))
              eq_refl Hrd with "Hcert Hf").
  Qed.

  Lemma wp_sllw_s_sconf
      (pc : mword 64) (rd rs1 rs2 : mword 5) (m : regfile) (n : nat) (b : bool) :
    let wval :=
      sign_extend' 64
        (shift_bits_left (subrange_vec_dec (rget m rs1) 31 0 : mword 32)
           (subrange_vec_dec (subrange_vec_dec (rget m rs2) 31 0 : mword 32) 4 0)) in
    uint rd <> 0 -> ops_ok b rd rs1 rs2 ->
    sie_cap_gpr KT1 m n b p -∗
    pc_is pc -∗ instr pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SLLW)) -∗
    wp_next b p (fun (CID : CpuId) =>
      sie_cap_gpr KT1 (<[Regidx rd := regval_into_reg wval]> m) n b p -∗
      pc_is (add_vec_int pc 4) -∗
      WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros wval Hrd Hops.
    exact (wp_sllw_wval_s_sconf pc rd rs1 rs2 wval m n b Hrd Hops eq_refl).
  Qed.

End WpSconfAlu.

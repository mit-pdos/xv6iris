(* WpUmodeLeaf.v -- the PER-INSTRUCTION leaves of the VERIFIED user-execution
   tier (claude-notes/projects/user-verified.md).

   Every leaf here is a thin wrapper over ONE of the two drivers in
   WpUmodeStep.v:

     [wp_uv_retire]  for a retiring, memory-preserving instruction: supply
                     the [uinstr] fact, the [ExecuteAs] expansion (if the
                     instruction is compressed / redirecting), the state
                     effect as an optional nextPC redirect [jt] and an
                     optional gpr write [wr], and the value-precise
                     [exec (execute ...)] fact at the post-fetch state;
     [wp_uv_ecall]   for [ecall].

   The leaf therefore says nothing about fetch geometry, interrupts,
   migration or minstret: an arbitrary number of pending interrupts is
   absorbed BEFORE the instruction retires (and each of them may migrate the
   process), which is why every continuation re-binds the hart.

   VALUE CONVENTION (claude-notes/design/code-organization.md,
   Specific-vs-generic): a leaf takes the written value as an explicit
   [wval] binder plus a PURE hypothesis fixing it, so the register file the
   continuation sees contains a closed term rather than a lookup into the
   map being updated. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras.
Require Import InstrBytes WpGpr RegFile.
Require Import ExecCommon WpMmodeLeafBase WpMmodeShiftiop.
Require Import UserBits.
Require Import UserPtTree UserExec.
Require Import UmodeMem UmodeCap.
Require Import WpUmodeStep.
Local Open Scope Z_scope.
Import Defs.
Set Printing Depth 40.

(* [exec_execute_JAL_gpr_zca] -- JAL's target-alignment check under the C
   extension: only bit 0 has to be clear (the decoder appends it), NOT bit
   1, because [jump_to] takes the Zca-relaxed branch.  A verbatim copy of
   WpSmodePtCtl.v's [Local Lemma] of the same name; RELOCATION DEBT: the
   operand-generic form belongs beside [exec_execute_JAL_gpr] in
   WpMmodeJal.v / WpMmodeLeafBase.v, but hoisting it there would rebuild
   the whole S-mode leaf tower, so it is kept Local here (as it already is
   in WpSmodePtCtl.v and WpSconfCtl.v -- three copies now). *)
Local Lemma exec_execute_JAL_gpr_zca (imm : mword 21) (rd : mword 5) s :
  uint rd <> 0 ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm (Regidx rd)) s
  = Some (RETIRE_SUCCESS,
          set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  (R_bitvector_64 (gpr_of_Z (uint rd)))
                  (regval_into_reg (register_lookup nextPC s.(sregs)))).
Proof.
  intros Hrd Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  match goal with |- context[Defs.bind0 ?wx _] =>
    assert (Hwx : exec wx (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                  = Some (tt, set_reg (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)))
                                (R_bitvector_64 (gpr_of_Z (uint rd)))
                                (regval_into_reg (register_lookup nextPC s.(sregs)))))
  end.
  { rewrite (exec_wX_bits_gpr rd (register_lookup nextPC s.(sregs)) _).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ Hwx).
  apply exec_returnm.
Qed.

(* [exec_execute_JAL_zreg_zca] -- the rd = x0 companion of the lemma above,
   needed by [wp_uv_cj]: c.j expands to [jal x0, off], which still sets
   nextPC but whose link write is the x0 no-op, so the post state has NO
   gpr layer at all.  Same Zca-relaxed alignment check (only bit 0).
   Another verbatim copy (WpSconfCtl.v and ProofSpin.v hold the others);
   RELOCATION DEBT: the operand-generic form belongs beside
   [exec_execute_JAL_gpr] in WpMmodeJal.v / WpMmodeLeafBase.v, but hoisting
   it there would rebuild the whole S-mode leaf tower. *)
Local Lemma exec_execute_JAL_zreg_zca (imm : mword 21) s :
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute_JAL imm zreg) s
  = Some (RETIRE_SUCCESS,
          set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
Proof.
  intros Halign Hzca.
  unfold execute_JAL, get_next_pc.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg nextPC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_jump_to_zca _ s Halign Hzca)).
  cbn match.
  unfold zreg.
  rewrite (exec_bind0_Some _ _ _ _ _
    (exec_wX_bits_gpr (zero_extend' 5 ('b"00")) (register_lookup nextPC s.(sregs))
       (set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))))).
  apply exec_returnm.
Qed.

(* [exec_execute_DIVU_gpr_uv] / [exec_execute_REMU_gpr_uv] -- the two
   M-extension execute facts at is_unsigned = true, operand-generic in the
   register triple.  DIVISION BY ZERO IS DEFINED in RISC-V (quotient
   all-ones, remainder the dividend) and the model implements exactly that,
   which is why neither carries a "divisor nonzero" side condition; taking
   is_unsigned = true is also what collapses the model's signed-overflow
   fixup.  RELOCATION DEBT: both already exist, in this exact shape, as
   WpMmodeMul.v's [exec_execute_DIVU_gpr]/[exec_execute_REMU_gpr] -- these
   copies exist only so the verified-user leaf layer need not Require the
   M-mode multiply chain; retire them in favour of the originals when the
   two files may meet. *)
Local Lemma exec_execute_DIVU_gpr_uv (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (to_bits_truncate 64
                  (if Z.eqb (uint (gpr_src rs2 s)) 0 then -1
                   else Z.quot (uint (gpr_src rs1 s)) (uint (gpr_src rs2 s)))))).
Proof.
  intro Hrd. unfold gpr_src.
  change (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)))
    with (execute_DIV (Regidx rs2) (Regidx rs1) (Regidx rd) true).
  unfold execute_DIV.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Local Lemma exec_execute_REMU_gpr_uv (rs2 rs1 rd : mword 5) s :
  uint rd <> 0 ->
  exec (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true))) s
  = Some (RETIRE_SUCCESS,
          set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
            (regval_into_reg
               (to_bits_truncate 64
                  (if Z.eqb (uint (gpr_src rs2 s)) 0 then uint (gpr_src rs1 s)
                   else Z.rem (uint (gpr_src rs1 s)) (uint (gpr_src rs2 s)))))).
Proof.
  intro Hrd. unfold gpr_src.
  change (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true)))
    with (execute_REM (Regidx rs2) (Regidx rs1) (Regidx rd) true).
  unfold execute_REM.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  cbn zeta.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_wX_bits_gpr rd _ s)).
  replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
  apply exec_returnm.
Qed.

Section WpUmodeLeaf.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.
  Context (C : ucfg) (pt : uptd).

  (* =================================================================== *)
  (* THE THREE GENERIC gpr-WRITE LEAVES, indexed by SOURCE ARITY rather   *)
  (* than by AST constructor.                                             *)
  (*                                                                      *)
  (* Every non-jumping, memory-preserving instruction that writes exactly *)
  (* one gpr has the same model shape: read 0/1/2 source registers, apply *)
  (* a pure function of those reads (and, for AUIPC, of the pc), write    *)
  (* rd.  So the op-specific content is exactly ONE value function [vf]   *)
  (* and ONE [exec (execute ...)] fact, both taken as parameters, and     *)
  (* ADD/SUB/AND/SLTU/ADDW/SUBW/DIVU/REMU (2 sources),                    *)
  (* ADDI/ANDI/XORI/SLTIU/SLLI/SRLI/SLLIW/ADDIW (1) and LUI/AUIPC (0) are *)
  (* CORROLARIES rather than clones.  This subsumes the earlier           *)
  (* [wp_uv_shiftiop] (which abstracted one family only): abstracting     *)
  (* over the AST CONSTRUCTOR as well costs nothing, because the funnel   *)
  (* already takes the instruction and its expansion as parameters.       *)
  (*                                                                      *)
  (* The same genericity covers the COMPRESSED half of each family for    *)
  (* free: the [ExecuteAs] expansion rides the funnel's own [o], so c.add *)
  (* is [wp_uv_alu2] at [o := Some (RTYPE ...)] and c.lui is              *)
  (* [wp_uv_alu0] at [o := Some (UTYPE ...)] -- no compressed-specific    *)
  (* engine exists or is needed.                                          *)
  (*                                                                      *)
  (* [gpr_src] (WpMmodeShiftiop.v) is the model's uniform register read   *)
  (* (x0 -> zero_reg), which is exactly what the funnel's register-read   *)
  (* premise equates to [m !!! _].  The [if uint rd =? 0] guard the exec  *)
  (* facts carry is kept in the premise, so a fact already in that shape  *)
  (* needs no bridge; the handful stated instead with a [uint rd <> 0]    *)
  (* hypothesis (AND / SLTU / DIVU / REMU) get a three-line [assert].     *)
  (*                                                                      *)
  (* TWO leaves below are deliberately NOT instances: [wp_uv_cli] and     *)
  (* [wp_uv_cmv] read x0 as a SOURCE and spell their written value with   *)
  (* [zero_reg], whereas an instance would have to state it as            *)
  (* [vf (m !!! Regidx x0)].  The two are equal -- the funnel's own       *)
  (* register-read premise pins [m !!! Regidx x0 = zero_reg] -- but only  *)
  (* INSIDE the proof, and the [wval] premise is consumed before that, so *)
  (* the conversion is not available where it would be needed.            *)
  (* =================================================================== *)

  (* zero sources: the value is fixed by the leaf, and the pc is offered  *)
  (* to the premise because AUIPC -- alone in this family -- reads it.    *)
  Lemma wp_uv_alu0 (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uint rd <> 0 ->
    (forall s : mstate,
       register_lookup PC s.(sregs) = pc ->
       exec (execute (uv_exp i o)) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg wval))) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hrd Hop.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc is_rvc i o None (Some (rd, wval))
              Hui Hred Hlpad Hrd with "Hcg Hpc Hcont").
    intros s_pc Lpc _ _ _ _.
    cbn [uv_post uv_jmp uv_wr].
    rewrite (Hop s_pc Lpc).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
  Qed.

  (* one source. *)
  Lemma wp_uv_alu1 (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (rs1 rd : mword 5) (vf : mword 64 -> mword 64) (wval : mword 64) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uint rd <> 0 ->
    (forall s : mstate,
       exec (execute (uv_exp i o)) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (vf (gpr_src rs1 s))))) ->
    wval = vf (m !!! Regidx rs1) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hrd Hop Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc is_rvc i o None (Some (rd, wval))
              Hui Hred Hlpad Hrd with "Hcg Hpc Hcont").
    intros s_pc _ _ _ _ Hvals.
    cbn [uv_post uv_jmp uv_wr].
    rewrite (Hop s_pc).
    unfold gpr_src. rewrite (Hvals rs1).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  (* two sources.  [rs1] and [rs2] are the LEMMA's own binders, so the two *)
  (* register-read rewrites below never collide even when a call site      *)
  (* instantiates them to the same index (c.add is rd += rs2).             *)
  Lemma wp_uv_alu2 (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (is_rvc : bool) (i : instruction) (o : option instruction)
      (rs1 rs2 rd : mword 5) (vf : mword 64 -> mword 64 -> mword 64)
      (wval : mword 64) :
    uinstr pt M pc is_rvc i ->
    uv_redirect i o ->
    is_lpad_instruction i = false ->
    uint rd <> 0 ->
    (forall s : mstate,
       exec (execute (uv_exp i o)) s
       = Some (RETIRE_SUCCESS,
               if Z.eqb (uint rd) 0 then s
               else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                      (regval_into_reg (vf (gpr_src rs1 s) (gpr_src rs2 s))))) ->
    wval = vf (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc (if is_rvc then 2 else 4)) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hred Hlpad Hrd Hop Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc is_rvc i o None (Some (rd, wval))
              Hui Hred Hlpad Hrd with "Hcg Hpc Hcont").
    intros s_pc _ _ _ _ Hvals.
    cbn [uv_post uv_jmp uv_wr].
    rewrite (Hop s_pc).
    unfold gpr_src. rewrite (Hvals rs1). rewrite (Hvals rs2).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.li rd, imm -- the pilot leaf.                                       *)
  (*                                                                       *)
  (* Compressed, so the retire funnel drives it through the [ExecuteAs]    *)
  (* expansion [C_LI (imm, rd) -> ITYPE (sign_extend' 12 imm, x0, rd,      *)
  (* ADDI)] ([exec_execute_C_LI]); no jump ([jt := None]), one gpr write    *)
  (* ([wr := Some (rd, wval)]), memory untouched.                          *)
  (*                                                                       *)
  (* [uint rd <> 0] is a PREMISE, not a consequence: [uinstr] only says     *)
  (* what the word decodes to, and the AST carries whatever index the       *)
  (* decoder produced (c.li with rd = x0 is a HINT the model still decodes  *)
  (* to [C_LI]).  Every real call site discharges it by [vm_compute].       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cli (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_LI (imm, Regidx rd)) ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc true (C_LI (imm, Regidx rd))
              (Some (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)))
              None (Some (rd, wval)) Hui
              ltac:(intro s; apply exec_execute_C_LI)
              eq_refl Hrd
              with "Hcg Hpc Hcont").
    intros s_pc _ _ _ _ _.
    cbn [uv_exp uv_post uv_jmp uv_wr].
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd
               (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    rewrite Hwval. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.addi rd, imm -- rd += sext(imm).  The sp-adjust of every prologue,  *)
  (* so rd = sp is the NORMAL case and must not be excluded: the funnel    *)
  (* constrains a gpr write only by [uv_wrok] (rd <> x0), and the register *)
  (* file's sp slot is an ordinary slot -- unlike the kernel's [sie_cap],  *)
  (* the verified user tier reserves no stack headroom, so moving sp is    *)
  (* just an arithmetic write.                                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_caddi (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_ADDI (imm, Regidx rd)) ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (sign_extend' 64 (sign_extend' 12 imm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc true (C_ADDI (imm, Regidx rd))
             (Some (ITYPE (sign_extend' 12 imm, Regidx rd, Regidx rd, ADDI)))
             rd rd (fun a => add_vec a (sign_extend' 64 (sign_extend' 12 imm)))
             wval Hui (fun s => exec_execute_C_ADDI imm (Regidx rd) s) eq_refl Hrd
             (fun s => exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm) s)
             Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.addi4spn rd', nzimm -- rd' := sp + zext(nzimm*4).  The compressed   *)
  (* frame-pointer set-up: base is ALWAYS sp, destination is a COMPRESSED  *)
  (* register index, so the leaf takes the expanded index [rd] with the    *)
  (* decoder's expansion as a pure premise (one [vm_compute] at the call). *)
  (* The immediate is the model's own [caddi4spn_imm] (a 12-bit ZERO-      *)
  (* extension of nzimm ++ 00), which the ADDI then sign-extends -- the    *)
  (* value form is taken verbatim from the execute fact.                   *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_caddi4spn (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (cr : mword 3) (nzimm : mword 8) (rd : mword 5)
      (wval : mword 64) :
    uinstr pt M pc true (C_ADDI4SPN (Cregidx cr, nzimm)) ->
    creg2reg_idx (Cregidx cr) = Regidx rd ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi4spn_imm nzimm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcr Hrd Hwval.
    assert (Hred : uv_redirect (C_ADDI4SPN (Cregidx cr, nzimm))
                     (Some (ITYPE (caddi4spn_imm nzimm, Regidx csp_rs1,
                                   Regidx rd, ADDI)))).
    { intro s. rewrite (exec_execute_C_ADDI4SPN (Cregidx cr) nzimm s).
      rewrite Hcr. reflexivity. }
    exact (wp_uv_alu1 Ψ M m pc true (C_ADDI4SPN (Cregidx cr, nzimm))
             (Some (ITYPE (caddi4spn_imm nzimm, Regidx csp_rs1, Regidx rd, ADDI)))
             csp_rs1 rd (fun a => add_vec a (sign_extend' 64 (caddi4spn_imm nzimm)))
             wval Hui Hred eq_refl Hrd
             (fun s => exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s)
             Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* jal rd, imm -- the base (4-byte) call: rd := pc+4 AND nextPC :=       *)
  (* target, so BOTH funnel layers fire ([jt] then [wr], in the model's    *)
  (* order).  The target's 2-alignment is all the C extension requires:    *)
  (* [jump_to] takes the Zca branch, and Zca is read off the funnel's      *)
  (* config agreement, so the leaf's only side condition is target bit 0   *)
  (* (a decoder invariant -- the immediate's low bit is appended -- that   *)
  (* every call site discharges by [vm_compute]).                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_jal (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 21) (rd : mword 5) (tgt wval : mword 64) :
    uinstr pt M pc false (JAL (imm, Regidx rd)) ->
    uint rd <> 0 ->
    tgt = add_vec pc (sign_extend' 64 imm) ->
    wval = add_vec_int pc 4 ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Htgt Hwval Hal0.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc false (JAL (imm, Regidx rd)) None
              (Some tgt) (Some (rd, wval)) Hui
              ltac:(intro s; exact I)
              eq_refl Hrd
              with "Hcg Hpc Hcont").
    intros s_pc Lpc Lnpc _ Hag _.
    cbn [uv_exp uv_post uv_jmp uv_wr].
    change (execute (JAL (imm, Regidx rd))) with (execute_JAL imm (Regidx rd)).
    rewrite (exec_execute_JAL_gpr_zca imm rd s_pc Hrd
               ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)
               (agree_u_zca s_pc Hag)).
    rewrite Lpc Lnpc. rewrite <- Htgt. rewrite Hwval. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.jr rs1 -- the function RETURN (c.jr ra).  Expands to                *)
  (* [jalr x0, 0(rs1)]: rd = x0, so the link write is a no-op and the      *)
  (* funnel's write layer is [wr := None] ([uv_wrok] is then vacuous and   *)
  (* the register file comes back UNCHANGED).  JALR clears bit 0 of the    *)
  (* target itself, so there is no alignment side condition at all; the    *)
  (* two extension gates it does consult (Zicfilp for [update_elp_state],  *)
  (* Zca for [jump_to]) come off the funnel's config agreement.            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cjr (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 : mword 5) (tgt : mword 64) :
    uinstr pt M pc true (C_JR (Regidx rs1)) ->
    uint rs1 <> 0 ->
    tgt = ret_pc (m !!! Regidx rs1) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrs1 Htgt.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc true (C_JR (Regidx rs1))
              (Some (JALR (zeros' 12, Regidx rs1, zreg)))
              (Some tgt) None Hui
              ltac:(intro s; apply exec_execute_C_JR)
              eq_refl I
              with "Hcg Hpc Hcont").
    intros s_pc _ _ _ Hag Hvals.
    cbn [uv_exp uv_post uv_jmp uv_wr uv_upd].
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = m !!! Regidx rs1).
    { pose proof (Hvals rs1) as Hv.
      replace (Z.eqb (uint rs1) 0) with false in Hv
        by (symmetry; apply Z.eqb_neq; exact Hrs1).
      exact Hv. }
    change (execute (JALR (zeros' 12, Regidx rs1, zreg)))
      with (execute_JALR (zeros' 12) (Regidx rs1) zreg).
    change zreg with (Regidx cli_rs1).
    rewrite (exec_execute_JALR_ret_zca (zeros' 12) rs1 cli_rs1 s_pc Hrs1
               ltac:(vm_compute; reflexivity)
               (agree_u_zicfilp s_pc Hag) (agree_u_zca s_pc Hag)
               ltac:(apply bit0_update0_64)).
    rewrite Hrsv. rewrite ret_pc_jalr. rewrite Htgt. reflexivity.
  Qed.

  (* =================================================================== *)
  (* COMPRESSED leaves (is_rvc = true, pc += 2, [o] = the ExecuteAs       *)
  (* expansion).                                                         *)
  (* =================================================================== *)

  (* ------------------------------------------------------------------- *)
  (* c.addi16sp nzimm -- sp += sext(nzimm*16), the 16-byte-granular stack  *)
  (* adjust of a NON-leaf prologue (0x7139 = addi sp,sp,-64).  Its source  *)
  (* AND destination are BOTH hard-wired to sp, so unlike c.addi it takes  *)
  (* no register operand at all and its [uv_wrok] is a closed fact         *)
  (* ([uint sp = 2 <> 0], discharged here rather than pushed on the        *)
  (* caller).  The immediate is the model's own [caddi16sp_imm].           *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_caddi16sp (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (wval : mword 64) :
    uinstr pt M pc true (C_ADDI16SP imm) ->
    wval = add_vec (m !!! Regidx csp_rs1)
             (sign_extend' 64 (caddi16sp_imm imm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx csp_rs1 := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hwval.
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    exact (wp_uv_alu1 Ψ M m pc true (C_ADDI16SP imm)
             (Some (ITYPE (caddi16sp_imm imm, Regidx csp_rs1, Regidx csp_rs1, ADDI)))
             csp_rs1 csp_rs1
             (fun a => add_vec a (sign_extend' 64 (caddi16sp_imm imm)))
             wval Hui (fun s => exec_execute_C_ADDI16SP imm s) eq_refl Hsp
             (fun s => exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1
                         (caddi16sp_imm imm) s)
             Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.mv rd, rs2 -- register move.  The model has no move: it expands to  *)
  (* [add rd, x0, rs2] ([exec_execute_C_MV]), so the leaf rides the        *)
  (* operand-generic [exec_execute_RTYPE_ADD_gpr] (WpGpr.v) with rs1 = x0  *)
  (* -- the SAME fact [wp_uv_add] below uses, which is why no ADD-specific *)
  (* helper is needed here.  The written value keeps the model's           *)
  (* [add_vec zero_reg _] shape (the [wp_uv_cli] convention), and rs2 = x0 *)
  (* needs no premise: the funnel's register-read fact is uniform in the   *)
  (* x0 case.                                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cmv (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rd rs2 : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_MV (Regidx rd, Regidx rs2)) ->
    uint rd <> 0 ->
    wval = add_vec zero_reg (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc true (C_MV (Regidx rd, Regidx rs2))
              (Some (RTYPE (Regidx rs2, zreg, Regidx rd, ADD)))
              None (Some (rd, wval)) Hui
              ltac:(intro s; apply exec_execute_C_MV)
              eq_refl Hrd
              with "Hcg Hpc Hcont").
    intros s_pc _ _ _ _ Hvals.
    cbn [uv_exp uv_post uv_jmp uv_wr].
    change zreg with (Regidx cli_rs1).
    change (execute (RTYPE (Regidx rs2, Regidx cli_rs1, Regidx rd, ADD)))
      with (execute_RTYPE (Regidx rs2) (Regidx cli_rs1) (Regidx rd) ADD).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 cli_rs1 rd s_pc).
    unfold gpr_rd_val.
    rewrite (Hvals rs2).
    replace (Z.eqb (uint cli_rs1) 0) with true by (vm_compute; reflexivity).
    replace (Z.eqb (uint rd) 0) with false
      by (symmetry; apply Z.eqb_neq; exact Hrd).
    rewrite Hwval. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.addiw rd, imm (0x3579) -- the 32-bit add-immediate: rd :=           *)
  (* sext32(rd + sext(imm)).  Source and destination coincide (like        *)
  (* c.addi), but the expansion is a base [ADDIW], NOT an [ITYPE], so the  *)
  (* value carries the model's truncate-then-sign-extend                   *)
  (* ([gpr_addiw_val]'s shape) -- this is C's `int` arithmetic, and the    *)
  (* leaf must not silently present it as 64-bit.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_caddiw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_ADDIW (imm, Regidx rd)) ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (subrange_vec_dec
                (add_vec (m !!! Regidx rd)
                         (sign_extend' 64 (sign_extend' 12 imm))) 31 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc true (C_ADDIW (imm, Regidx rd))
             (Some (ADDIW (sign_extend' 12 imm, Regidx rd, Regidx rd)))
             rd rd
             (fun a => sign_extend' 64
                         (subrange_vec_dec
                            (add_vec a (sign_extend' 64 (sign_extend' 12 imm)))
                            31 0))
             wval Hui (fun s => exec_execute_C_ADDIW imm (Regidx rd) s) eq_refl Hrd
             (fun s => exec_execute_ADDIW_gpr rd rd (sign_extend' 12 imm) s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* c.j off (0xa809 / 0xbfdd) -- the compressed unconditional jump, and   *)
  (* the compressed mirror of [wp_uv_jal]: it expands to [jal x0, off], so *)
  (* the link write is the x0 no-op and the leaf is a JUMP-ONLY funnel     *)
  (* instance ([jt := Some tgt], [wr := None], [uv_wrok] vacuous, register *)
  (* file unchanged).  That is exactly why [exec_execute_JAL_gpr_zca] --   *)
  (* which REQUIRES [uint rd <> 0] -- cannot serve it and the x0 companion *)
  (* [exec_execute_JAL_zreg_zca] is needed.  Zca comes off the funnel's    *)
  (* config agreement; the target's bit 0 (a decoder invariant: the        *)
  (* immediate is [imm ++ 0]) stays a call-site [vm_compute].              *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_cj (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 11) (tgt : mword 64) :
    uinstr pt M pc true (C_J imm) ->
    tgt = add_vec pc (sign_extend' 64 (sign_extend' 21 (concat_vec imm ('b"0")))) ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Htgt Hal0.
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc true (C_J imm)
              (Some (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)))
              (Some tgt) None Hui
              ltac:(intro s; apply exec_execute_C_J)
              eq_refl I
              with "Hcg Hpc Hcont").
    intros s_pc Lpc _ _ Hag _.
    cbn [uv_exp uv_post uv_jmp uv_wr uv_upd].
    change (execute (JAL (sign_extend' 21 (concat_vec imm ('b"0")), zreg)))
      with (execute_JAL (sign_extend' 21 (concat_vec imm ('b"0"))) zreg).
    rewrite (exec_execute_JAL_zreg_zca (sign_extend' 21 (concat_vec imm ('b"0"))) s_pc
               ltac:(rewrite Lpc; rewrite <- Htgt; exact Hal0)
               (agree_u_zca s_pc Hag)).
    rewrite Lpc. rewrite <- Htgt. reflexivity.
  Qed.

  (* =================================================================== *)
  (* BASE leaves (is_rvc = false, pc += 4, no ExecuteAs redirect).        *)
  (* =================================================================== *)

  (* ------------------------------------------------------------------- *)
  (* addi rd, rs1, imm -- the uncompressed add-immediate, reached whenever *)
  (* the immediate or a register index does not fit the RVC form.  It is   *)
  (* the SAME [exec_execute_ITYPE_ADDI_gpr] leaf [wp_uv_cli] /             *)
  (* [wp_uv_caddi] / [wp_uv_caddi4spn] reach through their expansions,     *)
  (* here with [o := None] and a 4-byte pc tick.  rs1 = x0 (the `li'       *)
  (* pseudo-instruction) needs no premise -- the funnel's register-read    *)
  (* fact is uniform in the x0 case.                                       *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_addi (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI)) ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ADDI))
             None rs1 rd (fun a => add_vec a (sign_extend' 64 imm)) wval Hui
             (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_ITYPE_ADDI_gpr rs1 rd imm s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* add rd, rs1, rs2 -- the two-source 64-bit add.  Shares                *)
  (* [exec_execute_RTYPE_ADD_gpr] with [wp_uv_cmv] (which is this          *)
  (* instruction at rs1 = x0), which is why that fact is stated            *)
  (* operand-generically.  Both sources may be x0.                         *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_add (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD)) ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu2 Ψ M m pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, ADD))
             None rs1 rs2 rd (fun a b => add_vec a b) wval Hui
             (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_RTYPE_ADD_gpr rs2 rs1 rd s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* The SHIFTIOP family.  The model's [execute_SHIFTIOP] is uniform in    *)
  (* the op -- read rs1, apply an op-indexed pure function of the source   *)
  (* and the shamt, write rd -- i.e. it is exactly [wp_uv_alu1]'s shape,   *)
  (* so slli/srli are direct instances and a third op (srai) costs a       *)
  (* corollary, not a clone.  There is no separate family engine: the      *)
  (* op-generic [wp_uv_shiftiop] this file used to carry said nothing      *)
  (* [wp_uv_alu1] does not.                                                *)
  (* ------------------------------------------------------------------- *)

  (* slli rd, rs1, shamt -- [wp_uv_alu1] at SLLI. *)
  Lemma wp_uv_slli (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI)) ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rs1)
             (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SLLI))
             None rs1 rd
             (fun a => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_SHIFTIOP_SLLI_gpr rs1 rd shamt s) Hwval).
  Qed.

  (* srli rd, rs1, shamt -- [wp_uv_alu1] at SRLI. *)
  Lemma wp_uv_srli (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (shamt : mword 6) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI)) ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rs1)
             (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (SHIFTIOP (shamt, Regidx rs1, Regidx rd, SRLI))
             None rs1 rd
             (fun a => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_SHIFTIOP_SRLI_gpr rs1 rd shamt s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* subw rd, rs1, rs2 -- the 32-bit subtract, sign-extended back to 64:   *)
  (* C's `int' difference.  RTYPEW, not RTYPE, so it does NOT share        *)
  (* [wp_uv_add]'s execute fact, and the value must expose the truncation  *)
  (* (both sources are cut to 32 bits BEFORE the subtract) -- a leaf that  *)
  (* presented [sub_vec] on the full 64 bits would be wrong.               *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_subw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW)) ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (sub_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32)
                      (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu2 Ψ M m pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, SUBW))
             None rs1 rs2 rd
             (fun a b => sign_extend' 64
                           (sub_vec (subrange_vec_dec a 31 0 : mword 32)
                                    (subrange_vec_dec b 31 0 : mword 32)))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_RTYPEW_SUBW_gpr rs2 rs1 rd s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* auipc rd, imm -- rd := pc + (imm << 12).  The only leaf here whose    *)
  (* written value is a function of the PROGRAM COUNTER rather than of the *)
  (* register file, so [wval] is pinned against [pc] and the funnel's      *)
  (* [register_lookup PC s_pc.(sregs) = pc] premise is what closes the gap *)
  (* (the same premise [wp_uv_jal] uses for its target).  Note the model   *)
  (* reads the ARCHITECTURAL pc, which at the post-fetch state is still    *)
  (* the instruction's own address -- the pc tick is the funnel's job.     *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_auipc (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 20) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (UTYPE (imm, Regidx rd, AUIPC)) ->
    uint rd <> 0 ->
    wval = add_vec pc (auipc_off imm) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    apply (wp_uv_alu0 Ψ M m pc false (UTYPE (imm, Regidx rd, AUIPC)) None rd wval
             Hui (fun _ : mstate => I) eq_refl Hrd).
    intros s Lpc. rewrite (exec_execute_UTYPE_AUIPC_gpr rd imm s).
    rewrite Lpc. rewrite Hwval. reflexivity.
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sub rd, rs1, rs2 -- the two-source 64-bit subtract.  [neg rd,rs] is   *)
  (* this instruction at rs1 = x0 and needs no premise for it: the         *)
  (* funnel's register-read fact is uniform in the x0 case.                *)
  (* [exec_execute_RTYPE_SUB_gpr] is already in [wp_uv_alu2]'s shape (it   *)
  (* carries the [if uint rd =? 0] guard itself), so the leaf is a pure    *)
  (* instance with no bridge.                                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sub (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB)) ->
    uint rd <> 0 ->
    wval = sub_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu2 Ψ M m pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SUB))
             None rs1 rs2 rd (fun a b => sub_vec a b) wval Hui
             (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_RTYPE_SUB_gpr rs2 rs1 rd s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* and rd, rs1, rs2.  Its execute fact is stated with a [uint rd <> 0]   *)
  (* HYPOTHESIS rather than with the [if uint rd =? 0] guard the rest of   *)
  (* the family carries, so the leaf spends three lines turning the one    *)
  (* shape into the other; the same [assert] appears in [wp_uv_sltu],      *)
  (* [wp_uv_divu] and [wp_uv_remu], which are the file's only other        *)
  (* consumers of a hypothesis-form fact.                                  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_and (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND)) ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hop : forall s : mstate,
              exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))) s
              = Some (RETIRE_SUCCESS,
                      if Z.eqb (uint rd) 0 then s
                      else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                             (regval_into_reg (and_vec (gpr_src rs1 s) (gpr_src rs2 s))))).
    { intro s.
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact (exec_execute_RTYPE_AND_gpr rs2 rs1 rd s Hrd). }
    exact (wp_uv_alu2 Ψ M m pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, AND))
             None rs1 rs2 rd (fun a b => and_vec a b) wval Hui
             (fun _ : mstate => I) eq_refl Hrd Hop Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sltu rd, rs1, rs2 -- the unsigned set-less-than, and the `snez rd,rs' *)
  (* pseudo-instruction (SLTU rd, x0, rs).  Its value is a BOOLEAN         *)
  (* zero-extended to 64 bits, not an arithmetic result, so the leaf must  *)
  (* present the model's [bool_to_bit (zopz0zI_u ...)] rather than a       *)
  (* comparison in the caller's own vocabulary.                            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sltu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU)) ->
    uint rd <> 0 ->
    wval = zero_extend' 64
             (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (m !!! Regidx rs2))) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hop : forall s : mstate,
              exec (execute (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))) s
              = Some (RETIRE_SUCCESS,
                      if Z.eqb (uint rd) 0 then s
                      else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                             (regval_into_reg
                                (zero_extend' 64
                                   (bool_to_bit (zopz0zI_u (gpr_src rs1 s)
                                                           (gpr_src rs2 s))))))).
    { intro s.
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact (exec_execute_RTYPE_SLTU_gpr rs2 rs1 rd s Hrd). }
    exact (wp_uv_alu2 Ψ M m pc false (RTYPE (Regidx rs2, Regidx rs1, Regidx rd, SLTU))
             None rs1 rs2 rd
             (fun a b => zero_extend' 64 (bool_to_bit (zopz0zI_u a b)))
             wval Hui (fun _ : mstate => I) eq_refl Hrd Hop Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* addw rd, rs1, rs2 -- the 32-bit add, sign-extended back to 64: C's    *)
  (* `int' sum, the mirror of the existing [wp_uv_subw].  RTYPEW, so the   *)
  (* value must expose the truncation of BOTH sources before the add.      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_addw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW)) ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (add_vec (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32)
                      (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu2 Ψ M m pc false (RTYPEW (Regidx rs2, Regidx rs1, Regidx rd, ADDW))
             None rs1 rs2 rd
             (fun a b => sign_extend' 64
                           (add_vec (subrange_vec_dec a 31 0 : mword 32)
                                    (subrange_vec_dec b 31 0 : mword 32)))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_RTYPEW_ADDW_gpr rs2 rs1 rd s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* sltiu rd, rs1, imm -- and, at imm = 1, the `seqz rd,rs' pseudo-       *)
  (* instruction (rd := (rs == 0)), which is how the shell tests a         *)
  (* pointer.  The immediate is SIGN-extended and the comparison is        *)
  (* UNSIGNED -- that mismatch is architectural, so the leaf presents the  *)
  (* model's [sign_extend' 64 imm] verbatim rather than a zero-extension.  *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_sltiu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU)) ->
    uint rd <> 0 ->
    wval = zero_extend' 64
             (bool_to_bit (zopz0zI_u (m !!! Regidx rs1) (sign_extend' 64 imm))) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (ITYPE (imm, Regidx rs1, Regidx rd, SLTIU))
             None rs1 rd
             (fun a => zero_extend' 64
                         (bool_to_bit (zopz0zI_u a (sign_extend' 64 imm))))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_ITYPE_SLTIU_gpr rs1 rd imm s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* andi rd, rs1, imm -- and, at imm = 255, `zext.b'.  The immediate is   *)
  (* sign-extended before the mask, which is why 255 is expressible in 12  *)
  (* bits at all.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_andi (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI)) ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (ITYPE (imm, Regidx rs1, Regidx rd, ANDI))
             None rs1 rd (fun a => and_vec a (sign_extend' 64 imm))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_ITYPE_ANDI_gpr rs1 rd imm s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* xori rd, rs1, imm -- and, at imm = -1, the `not rd,rs' pseudo-        *)
  (* instruction.                                                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_xori (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI)) ->
    uint rd <> 0 ->
    wval = xor_vec (m !!! Regidx rs1) (sign_extend' 64 imm) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (ITYPE (imm, Regidx rs1, Regidx rd, XORI))
             None rs1 rd (fun a => xor_vec a (sign_extend' 64 imm))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_ITYPE_XORI_gpr rs1 rd imm s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* addiw rd, rs1, imm -- the BASE 32-bit add-immediate, and at imm = 0   *)
  (* the `sext.w rd,rs' pseudo-instruction (which is how gcc materialises  *)
  (* a C `int' out of a 64-bit register).  The existing [wp_uv_caddiw] is  *)
  (* the COMPRESSED form and does not cover this one: c.addiw's source and *)
  (* destination coincide and its immediate is 6 bits, so `sext.w rd,rs'   *)
  (* with rd <> rs has no compressed encoding at all.                      *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_addiw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (ADDIW (imm, Regidx rs1, Regidx rd)) ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (subrange_vec_dec
                (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) 31 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (ADDIW (imm, Regidx rs1, Regidx rd))
             None rs1 rd
             (fun a => sign_extend' 64
                         (subrange_vec_dec (add_vec a (sign_extend' 64 imm)) 31 0))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_ADDIW_gpr rs1 rd imm s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* slliw rd, rs1, shamt -- the 32-bit shift-left-immediate.  The model's *)
  (* [execute_SHIFTIWOP] is uniform in the op exactly as [execute_SHIFTIOP]*)
  (* is (read rs1, truncate to 32, apply an op-indexed 32-bit shift,       *)
  (* sign-extend back), so this is again a direct [wp_uv_alu1] instance    *)
  (* and srliw/sraiw would each be one corollary.                          *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_slliw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (shamt : mword 5) (rs1 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW)) ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (shift_bits_left (subrange_vec_dec (m !!! Regidx rs1) 31 0 : mword 32)
                              shamt) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc false (SHIFTIWOP (shamt, Regidx rs1, Regidx rd, SLLIW))
             None rs1 rd
             (fun a => sign_extend' 64
                         (shift_bits_left (subrange_vec_dec a 31 0 : mword 32) shamt))
             wval Hui (fun _ : mstate => I) eq_refl Hrd
             (fun s => exec_execute_SHIFTIWOP_SLLIW_gpr rs1 rd shamt s) Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* lui rd, imm -- rd := sext(imm ++ 0x000).  The sibling of              *)
  (* [wp_uv_auipc] in the UTYPE family and the reason [wp_uv_alu0]'s       *)
  (* premise is offered the pc: LUI ignores it, AUIPC does not.            *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_lui (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 20) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (UTYPE (imm, Regidx rd, LUI)) ->
    uint rd <> 0 ->
    wval = luival imm ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    apply (wp_uv_alu0 Ψ M m pc false (UTYPE (imm, Regidx rd, LUI)) None rd wval
             Hui (fun _ : mstate => I) eq_refl Hrd).
    intros s _. rewrite Hwval. exact (exec_execute_UTYPE_LUI_gpr rd imm s).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* divu / remu rd, rs1, rs2 -- the two M-extension ops the shell uses    *)
  (* (printf's digit loop).  DIVISION BY ZERO IS DEFINED in RISC-V (the    *)
  (* quotient is all-ones, the remainder is the dividend) and the model    *)
  (* implements exactly that, so these leaves carry NO "divisor nonzero"   *)
  (* premise: the value function branches on the divisor instead, and a    *)
  (* caller that knows the divisor is nonzero simplifies its own copy.     *)
  (* Both are taken at [is_unsigned = true], which is what collapses the   *)
  (* model's signed-overflow fixup.                                        *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_divu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true)) ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64
             (if Z.eqb (uint (m !!! Regidx rs2)) 0 then -1
              else Z.quot (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hop : forall s : mstate,
              exec (execute (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))) s
              = Some (RETIRE_SUCCESS,
                      if Z.eqb (uint rd) 0 then s
                      else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                             (regval_into_reg
                                (to_bits_truncate 64
                                   (if Z.eqb (uint (gpr_src rs2 s)) 0 then -1
                                    else Z.quot (uint (gpr_src rs1 s))
                                                (uint (gpr_src rs2 s))))))).
    { intro s.
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact (exec_execute_DIVU_gpr_uv rs2 rs1 rd s Hrd). }
    exact (wp_uv_alu2 Ψ M m pc false (DIV (Regidx rs2, Regidx rs1, Regidx rd, true))
             None rs1 rs2 rd
             (fun a b => to_bits_truncate 64
                           (if Z.eqb (uint b) 0 then -1 else Z.quot (uint a) (uint b)))
             wval Hui (fun _ : mstate => I) eq_refl Hrd Hop Hwval).
  Qed.

  Lemma wp_uv_remu (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rs1 rs2 rd : mword 5) (wval : mword 64) :
    uinstr pt M pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true)) ->
    uint rd <> 0 ->
    wval = to_bits_truncate 64
             (if Z.eqb (uint (m !!! Regidx rs2)) 0 then uint (m !!! Regidx rs1)
              else Z.rem (uint (m !!! Regidx rs1)) (uint (m !!! Regidx rs2))) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 4) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    assert (Hop : forall s : mstate,
              exec (execute (REM (Regidx rs2, Regidx rs1, Regidx rd, true))) s
              = Some (RETIRE_SUCCESS,
                      if Z.eqb (uint rd) 0 then s
                      else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                             (regval_into_reg
                                (to_bits_truncate 64
                                   (if Z.eqb (uint (gpr_src rs2 s)) 0
                                    then uint (gpr_src rs1 s)
                                    else Z.rem (uint (gpr_src rs1 s))
                                               (uint (gpr_src rs2 s))))))).
    { intro s.
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact (exec_execute_REMU_gpr_uv rs2 rs1 rd s Hrd). }
    exact (wp_uv_alu2 Ψ M m pc false (REM (Regidx rs2, Regidx rs1, Regidx rd, true))
             None rs1 rs2 rd
             (fun a b => to_bits_truncate 64
                           (if Z.eqb (uint b) 0 then uint a else Z.rem (uint a) (uint b)))
             wval Hui (fun _ : mstate => I) eq_refl Hrd Hop Hwval).
  Qed.

  (* ------------------------------------------------------------------- *)
  (* jalr rd, imm(rs1) -- the base indirect jump, covering BOTH the        *)
  (* linking form and `jr rs1' (rd = x0) in ONE leaf: the two differ only  *)
  (* in the funnel's write layer, so [wr] is a parameter and the premise   *)
  (* below says which of the two shapes it is.  Cloning the surrounding    *)
  (* thirty lines per form would be a near-duplicate; the corollary        *)
  (* [wp_uv_jr] recovers the common rd = x0 case with the register file    *)
  (* spelled [m] rather than [uv_upd m None].                              *)
  (*                                                                       *)
  (* JALR clears bit 0 of the target itself, so there is NO alignment side *)
  (* condition; the two extension gates it consults (Zicfilp for           *)
  (* [update_elp_state], Zca for [jump_to]) come off the funnel's config   *)
  (* agreement.  [uint rs1 <> 0] IS required -- both exec facts read the   *)
  (* base register through the nonzero branch.                             *)
  (* ------------------------------------------------------------------- *)
  Lemma wp_uv_jalr (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5)
      (wr : option (mword 5 * mword 64)) (tgt : mword 64) :
    uinstr pt M pc false (JALR (imm, Regidx rs1, Regidx rd)) ->
    uint rs1 <> 0 ->
    (uint rd = 0 /\ wr = None) \/
    (uint rd <> 0 /\ wr = Some (rd, add_vec_int pc 4)) ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M (uv_upd m wr) -∗
       pc_is (CID := CID0) tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrs1 Hwr Htgt.
    assert (Hwrok : uv_wrok wr).
    { destruct Hwr as [[_ ->] | [Hrd ->]]; [ exact I | exact Hrd ]. }
    iIntros "Hcg Hpc Hcont".
    iApply (wp_uv_retire C pt Ψ M m pc false (JALR (imm, Regidx rs1, Regidx rd))
              None (Some tgt) wr Hui (fun _ : mstate => I) eq_refl Hwrok
              with "Hcg Hpc Hcont").
    intros s_pc _ Lnpc _ Hag Hvals.
    assert (Hrsv : register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs)
                   = m !!! Regidx rs1).
    { pose proof (Hvals rs1) as Hv.
      replace (Z.eqb (uint rs1) 0) with false in Hv
        by (symmetry; apply Z.eqb_neq; exact Hrs1).
      exact Hv. }
    change (execute (uv_exp (JALR (imm, Regidx rs1, Regidx rd)) None))
      with (execute_JALR imm (Regidx rs1) (Regidx rd)).
    destruct Hwr as [[Hrd0 Hw] | [Hrd0 Hw]]; subst wr.
    - rewrite (exec_execute_JALR_ret_zca imm rs1 rd s_pc Hrs1 Hrd0
                 (agree_u_zicfilp s_pc Hag) (agree_u_zca s_pc Hag)
                 ltac:(apply bit0_update0_64)).
      cbn [uv_post uv_jmp uv_wr].
      rewrite Hrsv. rewrite Htgt. unfold ret_pc. reflexivity.
    - rewrite (exec_execute_JALR_link_zca imm rs1 rd s_pc Hrs1 Hrd0
                 (agree_u_zicfilp s_pc Hag) (agree_u_zca s_pc Hag)
                 ltac:(apply bit0_update0_64)).
      cbn [uv_post uv_jmp uv_wr].
      rewrite Hrsv. rewrite Lnpc. rewrite Htgt. unfold ret_pc. reflexivity.
  Qed.

  (* jr rs1 -- [wp_uv_jalr] at rd = x0, where the register file is         *)
  (* untouched.  (`ret' is the COMPRESSED form of this and has its own     *)
  (* leaf, [wp_uv_cjr].) *)
  Lemma wp_uv_jr (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 12) (rs1 rd : mword 5) (tgt : mword 64) :
    uinstr pt M pc false (JALR (imm, Regidx rs1, Regidx rd)) ->
    uint rs1 <> 0 ->
    uint rd = 0 ->
    tgt = ret_pc (add_vec (m !!! Regidx rs1) (sign_extend' 64 imm)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M m -∗
       pc_is (CID := CID0) tgt -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrs1 Hrd Htgt.
    exact (wp_uv_jalr Ψ M m pc imm rs1 rd None tgt Hui Hrs1
             (or_introl (conj Hrd eq_refl)) Htgt).
  Qed.

  (* =================================================================== *)
  (* The COMPRESSED half of the ALU families.  Each is the SAME generic   *)
  (* leaf as its base sibling, at [o := Some <the ExecuteAs expansion>]   *)
  (* and [is_rvc := true] (pc += 2) -- no compressed-specific engine.     *)
  (* The creg-form ones (c.and, c.addw, c.srli) additionally take the     *)
  (* expanded 5-bit index with the decoder's expansion as a pure premise, *)
  (* one [vm_compute] at the call site, exactly as [wp_uv_caddi4spn].     *)
  (* =================================================================== *)

  (* c.add rd, rs2 (rd += rs2) -- the register-form compressed add.  Its  *)
  (* expansion's rs1 and rd COINCIDE, which is harmless: [wp_uv_alu2]'s   *)
  (* two register-read rewrites are over its own distinct binders.        *)
  Lemma wp_uv_cadd (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (rd rs2 : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_ADD (Regidx rd, Regidx rs2)) ->
    uint rd <> 0 ->
    wval = add_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu2 Ψ M m pc true (C_ADD (Regidx rd, Regidx rs2))
             (Some (RTYPE (Regidx rs2, Regidx rd, Regidx rd, ADD)))
             rd rs2 rd (fun a b => add_vec a b) wval Hui
             (fun s => exec_execute_C_ADD (Regidx rd) (Regidx rs2) s) eq_refl Hrd
             (fun s => exec_execute_RTYPE_ADD_gpr rs2 rd rd s) Hwval).
  Qed.

  (* c.and rd', rs2' -- creg-form, expanding to RTYPE AND. *)
  Lemma wp_uv_cand (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_AND (Cregidx crd, Cregidx crs2)) ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = and_vec (m !!! Regidx rd) (m !!! Regidx rs2) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcrd Hcrs2 Hrd Hwval.
    assert (Hred : uv_redirect (C_AND (Cregidx crd, Cregidx crs2))
                     (Some (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND)))).
    { intro s. rewrite (exec_execute_C_AND (Cregidx crd) (Cregidx crs2) s).
      rewrite Hcrd. rewrite Hcrs2. reflexivity. }
    assert (Hop : forall s : mstate,
              exec (execute (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND))) s
              = Some (RETIRE_SUCCESS,
                      if Z.eqb (uint rd) 0 then s
                      else set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                             (regval_into_reg (and_vec (gpr_src rd s) (gpr_src rs2 s))))).
    { intro s.
      replace (Z.eqb (uint rd) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hrd).
      exact (exec_execute_RTYPE_AND_gpr rs2 rd rd s Hrd). }
    exact (wp_uv_alu2 Ψ M m pc true (C_AND (Cregidx crd, Cregidx crs2))
             (Some (RTYPE (Regidx rs2, Regidx rd, Regidx rd, AND)))
             rd rs2 rd (fun a b => and_vec a b) wval Hui Hred eq_refl Hrd Hop Hwval).
  Qed.

  (* c.addw rd', rs2' -- creg-form, expanding to RTYPEW ADDW (C's `int'    *)
  (* add-assign). *)
  Lemma wp_uv_caddw (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (crd crs2 : mword 3) (rd rs2 : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_ADDW (Cregidx crd, Cregidx crs2)) ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    creg2reg_idx (Cregidx crs2) = Regidx rs2 ->
    uint rd <> 0 ->
    wval = sign_extend' 64
             (add_vec (subrange_vec_dec (m !!! Regidx rd) 31 0 : mword 32)
                      (subrange_vec_dec (m !!! Regidx rs2) 31 0 : mword 32)) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcrd Hcrs2 Hrd Hwval.
    assert (Hred : uv_redirect (C_ADDW (Cregidx crd, Cregidx crs2))
                     (Some (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW)))).
    { intro s. rewrite (exec_execute_C_ADDW (Cregidx crd) (Cregidx crs2) s).
      rewrite Hcrd. rewrite Hcrs2. reflexivity. }
    exact (wp_uv_alu2 Ψ M m pc true (C_ADDW (Cregidx crd, Cregidx crs2))
             (Some (RTYPEW (Regidx rs2, Regidx rd, Regidx rd, ADDW)))
             rd rs2 rd
             (fun a b => sign_extend' 64
                           (add_vec (subrange_vec_dec a 31 0 : mword 32)
                                    (subrange_vec_dec b 31 0 : mword 32)))
             wval Hui Hred eq_refl Hrd
             (fun s => exec_execute_RTYPEW_ADDW_gpr rs2 rd rd s) Hwval).
  Qed.

  (* c.lui rd, imm -- the compressed load-upper-immediate.  The decoder's  *)
  (* 6-bit immediate is SIGN-extended to the base form's 20 bits BEFORE    *)
  (* [luival] shifts it, which is what lets c.lui reach the negative       *)
  (* constants gcc uses for address bases.                                 *)
  Lemma wp_uv_clui (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (imm : mword 6) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_LUI (imm, Regidx rd)) ->
    uint rd <> 0 ->
    wval = luival (sign_extend' 20 imm) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    apply (wp_uv_alu0 Ψ M m pc true (C_LUI (imm, Regidx rd))
             (Some (UTYPE (sign_extend' 20 imm, Regidx rd, LUI))) rd wval Hui
             (fun s => exec_execute_C_LUI imm (Regidx rd) s) eq_refl Hrd).
    intros s _. rewrite Hwval.
    exact (exec_execute_UTYPE_LUI_gpr rd (sign_extend' 20 imm) s).
  Qed.

  (* c.slli rd, shamt -- register-form (NOT creg), source = destination.   *)
  Lemma wp_uv_cslli (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (shamt : mword 6) (rd : mword 5) (wval : mword 64) :
    uinstr pt M pc true (C_SLLI (shamt, Regidx rd)) ->
    uint rd <> 0 ->
    wval = shift_bits_left (m !!! Regidx rd)
             (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hrd Hwval.
    exact (wp_uv_alu1 Ψ M m pc true (C_SLLI (shamt, Regidx rd))
             (Some (SHIFTIOP (shamt, Regidx rd, Regidx rd, SLLI))) rd rd
             (fun a => shift_bits_left a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
             wval Hui (fun s => exec_execute_C_SLLI shamt (Regidx rd) s) eq_refl Hrd
             (fun s => exec_execute_SHIFTIOP_SLLI_gpr rd rd shamt s) Hwval).
  Qed.

  (* c.srli rd', shamt -- creg-form, source = destination. *)
  Lemma wp_uv_csrli (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)
      (pc : mword 64) (shamt : mword 6) (crd : mword 3) (rd : mword 5)
      (wval : mword 64) :
    uinstr pt M pc true (C_SRLI (shamt, Cregidx crd)) ->
    creg2reg_idx (Cregidx crd) = Regidx rd ->
    uint rd <> 0 ->
    wval = shift_bits_right (m !!! Regidx rd)
             (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0) ->
    uv_cap_gpr C pt Ψ M m -∗
    pc_is pc -∗
    (∀ CID0 : CpuId,
       uv_cap_gpr (CID := CID0) C pt Ψ M
         (<[Regidx rd := regval_into_reg wval]> m) -∗
       pc_is (CID := CID0) (add_vec_int pc 2) -∗
       WP (Loop : expr riscv_lang)) -∗
    WP (Loop : expr riscv_lang).
  Proof.
    intros Hui Hcrd Hrd Hwval.
    assert (Hred : uv_redirect (C_SRLI (shamt, Cregidx crd))
                     (Some (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI)))).
    { intro s. rewrite (exec_execute_C_SRLI shamt (Cregidx crd) s).
      rewrite Hcrd. reflexivity. }
    exact (wp_uv_alu1 Ψ M m pc true (C_SRLI (shamt, Cregidx crd))
             (Some (SHIFTIOP (shamt, Regidx rd, Regidx rd, SRLI))) rd rd
             (fun a => shift_bits_right a (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
             wval Hui Hred eq_refl Hrd
             (fun s => exec_execute_SHIFTIOP_SRLI_gpr rd rd shamt s) Hwval).
  Qed.

End WpUmodeLeaf.

(* ---------------------------------------------------------------------- *)
(* END-TO-END smoke check (validated by compiling this block against       *)
(* UCodeSync.v; it is kept as a COMMENT because WpUmodeLeaf.v is the        *)
(* program-GENERIC leaf layer and must not depend on a per-program          *)
(* [UCode<Prog>.v] -- the real call sites live in Proof<Prog>Prog.v):       *)
(*                                                                          *)
(*   Require Import UCodeSync.                                              *)
(*   Section Smoke.                                                         *)
(*     Context `{!riscvGS Σ}.                                               *)
(*     Context `{GEN : GenId} `{CID : CpuId}.                               *)
(*     Context (C : ucfg) (pt : uptd).                                      *)
(*     Example wp_uv_cli_at_sync_0c                                         *)
(*         (Ψ : usys_protocol Σ) (M : gmap Z (bv 8)) (m : regfile)          *)
(*         (Φ : mval -> iProp Σ) :                                          *)
(*       sync_layout pt -> sync_text_sub M ->                               *)
(*       uv_cap_gpr C pt Ψ M m -∗                                           *)
(*       pc_is (mword_of_int 0x0c) -∗                                       *)
(*       (∀ CID0 : CpuId,                                                   *)
(*          uv_cap_gpr (CID := CID0) C pt Ψ M                               *)
(*            (<[Regidx (mword_of_int 10) := regval_into_reg               *)
(*                 (add_vec zero_reg (sign_extend' 64                       *)
(*                    (sign_extend' 12 (mword_of_int 0 : mword 6))))]> m) -∗*)
(*          pc_is (CID := CID0) (add_vec_int (mword_of_int 0x0c) 2) -∗      *)
(*          WP (Loop : expr riscv_lang) {{ Φ }}) -∗                          *)
(*       WP (Loop : expr riscv_lang) {{ Φ }}.                                *)
(*     Proof.                                                               *)
(*       intros Hlay Hsub.                                                   *)
(*       exact (wp_uv_cli C pt Ψ M m (mword_of_int 0x0c) (mword_of_int 0)   *)
(*                (mword_of_int 10) _ Φ (ui_sync_0c pt M Hlay Hsub)         *)
(*                ltac:(vm_compute; discriminate) eq_refl).                  *)
(*     Qed.                                                                 *)
(*   End Smoke.                                                             *)
(* ---------------------------------------------------------------------- *)

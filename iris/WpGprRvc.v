(* WpGprRvc.v -- register-generic RVC (compressed, 2-byte) instruction WPs,
   ported to the NEW [wp_instr] / [mmode_config] / [gpr_file] layer (cf.
   WpGprAddi / WpGprLoad / WpGprStore / WpGprJalr).  Every WP here uses
   [is_rvc = true]: the fetch reads a 2-byte compressed halfword (packaged by
   [instr pc true i] via [instr_bytes]'s F_RVC case, which handles BOTH the
   4-aligned and 2-aligned fetch geometries -- so the old "_4-aligned" split
   collapses to ONE WP per op), and the execute advances nextPC by 2 (NOT 4)
   and goes through the [ExecuteAs] expansion: the compressed instr [i] first
   [ExecuteAs]-expands to the base instruction [other], which then executes to
   RETIRE_SUCCESS.  The ExecuteAs-expansion facts (the exec_execute_C_ lemmas)
   and the base-execute facts (exec_execute_ITYPE_ADDI_gpr, _UTYPE_LUI_gpr,
   the _SHIFTIOP_ / _RTYPE_ family, _ADDIW_gpr, _LOAD_8_gpr, _STORE_8_gpr) are
   representation-independent and REUSED verbatim from the base-instruction
   development. *)
From Stdlib Require Import Eqdep_dec ZArith Lia.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec RiscvExtras WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpGpr WpGprAddi WpGprLui WpGprShift WpGprLogic WpGprLoad WpGprJalr WpGprStore.
Require Import MinstretInv InstrBytes.
From iris.base_logic.lib Require Import invariants.
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.

(* ===================================================================== *)
(* RVC operand encodings (reused verbatim from the old WpRvc.v).          *)
(* ===================================================================== *)
Definition cli_rs1 : mword 5 := zero_extend' 5 ('b"00").
Definition csp_rs1 : mword 5 := zero_extend' 5 ('b"10").
Definition caddi16sp_imm (imm : mword 6) : mword 12 := sign_extend' 12 (concat_vec imm (Ox"0")).
Definition caddi4spn_imm (nzimm : mword 8) : mword 12 := concat_vec ('b"00") (concat_vec nzimm ('b"00")).

(* ===================================================================== *)
(* ExecuteAs-expansion facts: exec (execute (C_..)) = ExecuteAs base.       *)
(* Representation-independent; reused verbatim.                            *)
(* ===================================================================== *)
Lemma exec_execute_C_LI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LI (imm, rd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, zreg, rd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LI. apply exec_returnM. Qed.

Lemma exec_execute_C_LUI (imm : mword 6) (rd : regidx) s :
  exec (execute (C_LUI (imm, rd))) s
    = Some (ExecuteAs (UTYPE (sign_extend' 20 imm, rd, LUI)), s).
Proof. unfold execute. cbn match. unfold execute_C_LUI. apply exec_returnM. Qed.

Lemma exec_execute_C_SRLI (shamt : mword 6) (crsd : cregidx) s :
  exec (execute (C_SRLI (shamt, crsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, creg2reg_idx crsd, creg2reg_idx crsd, SRLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SRLI. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SLLI (shamt : mword 6) (rsd : regidx) s :
  exec (execute (C_SLLI (shamt, rsd))) s
    = Some (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)), s).
Proof. unfold execute. cbn match. unfold execute_C_SLLI. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_MV (rd rs2 : regidx) s :
  exec (execute (C_MV (rd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_MV. apply exec_returnM. Qed.

Lemma exec_execute_C_ADD (rsd rs2 : regidx) s :
  exec (execute (C_ADD (rsd, rs2))) s = Some (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADD. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDI (imm, rsd))) s
    = Some (ExecuteAs (ITYPE (sign_extend' 12 imm, rsd, rsd, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI16SP (imm : mword 6) s :
  exec (execute (C_ADDI16SP imm)) s
    = Some (ExecuteAs (ITYPE (caddi16sp_imm imm, sp, sp, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI16SP, caddi16sp_imm. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDI4SPN (rdc : cregidx) (nzimm : mword 8) s :
  exec (execute (C_ADDI4SPN (rdc, nzimm))) s
    = Some (ExecuteAs (ITYPE (caddi4spn_imm nzimm, sp, creg2reg_idx rdc, ADDI)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDI4SPN, caddi4spn_imm. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_OR (rsd rs2 : cregidx) s :
  exec (execute (C_OR (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, OR)), s).
Proof. unfold execute. cbn match. unfold execute_C_OR. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_AND (rsd rs2 : cregidx) s :
  exec (execute (C_AND (rsd, rs2))) s
    = Some (ExecuteAs (RTYPE (creg2reg_idx rs2, creg2reg_idx rsd, creg2reg_idx rsd, AND)), s).
Proof. unfold execute. cbn match. unfold execute_C_AND. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_ADDIW (imm : mword 6) (rsd : regidx) s :
  exec (execute (C_ADDIW (imm, rsd))) s
  = Some (ExecuteAs (ADDIW (sign_extend' 12 imm, rsd, rsd)), s).
Proof. unfold execute. cbn match. unfold execute_C_ADDIW. apply exec_returnM. Qed.

Lemma exec_execute_C_LD (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LD (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LD. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_LDSP (uimm : mword 6) (rd : regidx) s :
  exec (execute (C_LDSP (uimm, rd))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"000")), sp, rd, false, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_LDSP. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_SDSP (uimm : mword 6) (rs2 : regidx) s :
  exec (execute (C_SDSP (uimm, rs2))) s
  = Some (ExecuteAs (STORE (zero_extend' 12 (concat_vec uimm ('b"000")), rs2, sp, 8)), s).
Proof. unfold execute. cbn match. unfold execute_C_SDSP. cbn zeta. apply exec_returnM. Qed.

Lemma exec_execute_C_JR (rs1 : regidx) s :
  exec (execute (C_JR rs1)) s = Some (ExecuteAs (JALR (zeros' 12, rs1, zreg)), s).
Proof. unfold execute. cbn match. unfold execute_C_JR. apply exec_returnM. Qed.

(* ===================================================================== *)
(* GENERIC RVC gpr-write WP engine.  Any compressed instruction [ci] that   *)
(* [ExecuteAs]-expands to a base instruction [base] which writes ONE gpr    *)
(* [rd] the value [wval] (a function of the execute-state register file),    *)
(* stated on the [instr] / [mmode_config] / [gpr_file] layer with            *)
(* [is_rvc = true].  Mirrors [wp_addi_gpr] but: nextPC ticks +2, and the     *)
(* execute obligation is the RVC [ExecuteAs base] ; base-executes chain.     *)
(* The caller supplies, for the concrete op:                                 *)
(*   - Hexp : the ExecuteAs expansion of [ci] to [base] (unchanged by state);*)
(*   - Hbexec : the base execute at the ticked state writes rd := wval σ';    *)
(*   - Hval : the abstract written value [wval σ'] in terms of [m] lookups.   *)
(* ===================================================================== *)
Section RvcGprWrite.
  Context `{!riscvGS Σ}.

  (* The engine reads up to two source registers [rsa]/[rsb] off the [gpr_file]
     (at the ticked execute-state) and hands their values ([m !!! rsa] etc.) to
     the caller's execute obligation [Hbexec], so the abstract written value
     [wval] can be expressed in terms of the file [m].  Sources may be x0
     ([gpr_pt_value] reads them uniformly, giving [zero_reg] when the AST uses
     [zreg]); ops with fewer than two real sources just point [rsa]/[rsb] at any
     in-file register and ignore the value.  [Hbexec] is proven with the
     [s_pc]-lookup facts [Lva]/[Lvb] in scope, which is exactly what the base
     [_gpr] value lemmas (gpr_addi_val_file, gpr_srli_val_file, ...) consume. *)
  Lemma wp_rvc_gpr_write E (Φ : mval -> iProp Σ) (pc : mword 64) (rd rsa rsb : mword 5)
      (ci base : instruction) (wval : mword 64)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint rd <> 0 ->
    (* the ExecuteAs expansion of the compressed instr, at any state s *)
    (forall s : mstate, exec (execute ci) s = Some (ExecuteAs base, s)) ->
    (* the base execute, at the ticked execute-state s_pc, writes rd := wval,
       given the two source lookups at s_pc. *)
    (forall s_pc : mstate,
       register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2 ->
       (if Z.eqb (uint rsa) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsa))) s_pc.(sregs)) = m !!! Regidx rsa ->
       (if Z.eqb (uint rsb) 0 then zero_reg
        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rsb))) s_pc.(sregs)) = m !!! Regidx rsb ->
       exec (execute base) s_pc
       = Some (RETIRE_SUCCESS,
               set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval))) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true ci -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg wval]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Hexp Hbexec) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr E Φ pc true ci pmpcfg0 HN Hpmp with "Hmm Hpmpc Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rsa = Some (m !!! Regidx rsa))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmb : m !! Regidx rsb = Some (m !!! Regidx rsb))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    (* tick nextPC := pc+2 *)
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Lnpc0 : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    (* read source rsa off the file (borrow, read, return) *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rsa (m !!! Regidx rsa) s_pc with "Hreg Hrac") as %Lva0.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    (* read source rsb off the file *)
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rsb (m !!! Regidx rsb) s_pc with "Hreg Hrbc") as %Lvb0.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    (* write rd (rd <> 0, so its entry is the real register points-to) *)
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _ (regval_into_reg wval)
            with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg wval) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).
    (* RVC execute obligation: ExecuteAs base, then base retires *)
    iSplitR.
    { iExists base. iSplitR.
      - iPureIntro. rewrite Hpceq. fold s_pc. apply Hexp.
      - iPureIntro. rewrite Hpceq. fold s_pc. exact (Hbexec s_pc Lnpc0 Lva0 Lvb0). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg wval)).(sregs)
             = add_vec_int pc 2).
    { tmig. exact Lnpc0. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hmm' Hpmpc' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.
End RvcGprWrite.

(* ===================================================================== *)
(* Concrete register-write RVC WPs.  Each instantiates [wp_rvc_gpr_write]  *)
(* with the op's ExecuteAs fact + base [_gpr] execute; the written value    *)
(* is expressed via [m] lookups by rewriting with the source-lookup         *)
(* hypotheses the engine supplies.  Sources may be x0.                      *)
(* ===================================================================== *)
(* sign-extending imm6 to 12 bits then to 64 is the same as extending it to 64
   directly (nested sign extension collapses); lets the RVC ADDI/ADDIW WPs state
   the write value with a single [sign_extend' 64 imm6]. *)
Lemma sext6_12_64 (x : mword 6) : sign_extend' 64 (sign_extend' 12 x) = sign_extend' 64 x.
Proof.
  cbv [sign_extend' Operators_mwords.sign_extend Operators_mwords.exts_vec to_word get_word
       MachineWord.MachineWord.sign_extend].
  apply bv_eq_signed.
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  rewrite bv_sign_extend_signed; [| done].
  reflexivity.
Qed.

(* adding the zero register is a noop (used by c.li = addi rd,x0 and c.mv = add rd,x0). *)
Lemma add_vec_zero_l (x : mword 64) : add_vec zero_reg x = x.
Proof. apply bv_add_0_l. vm_compute. reflexivity. Qed.

Section RvcOps.
  Context `{!riscvGS Σ}.

  (* ---- c.li rd, imm6  =  addi rd, x0, sext(imm6) ---- *)
  Definition cli_wval (imm6 : mword 6) : mword 64 :=
    sign_extend' 64 imm6.

  Lemma wp_cli_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5) (imm6 : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_LI (imm6, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (cli_wval imm6)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rd cli_rs1 cli_rs1
              (C_LI (imm6, Regidx rd)) (ITYPE (sign_extend' 12 imm6, zreg, Regidx rd, ADDI))
              (cli_wval imm6) m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_LI imm6 (Regidx rd) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc _ _.
    change zreg with (Regidx cli_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr cli_rs1 rd (sign_extend' 12 imm6) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val, cli_wval, cli_rs1.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00"))) 0) with true by (vm_compute; reflexivity).
    rewrite add_vec_zero_l. rewrite sext6_12_64. reflexivity.
  Qed.

  (* ---- c.addi rd, imm6  =  addi rd, rd, sext(imm6) ---- *)
  Lemma wp_caddi_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5) (imm6 : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_ADDI (imm6, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd :=
        regval_into_reg (add_vec (m !!! Regidx rd) (sign_extend' 64 imm6))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rd rd rd
              (C_ADDI (imm6, Regidx rd)) (ITYPE (sign_extend' 12 imm6, Regidx rd, Regidx rd, ADDI))
              (add_vec (m !!! Regidx rd) (sign_extend' 64 imm6)) m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_ADDI imm6 (Regidx rd) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ITYPE_ADDI_gpr rd rd (sign_extend' 12 imm6) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val. rewrite Hva. rewrite sext6_12_64. reflexivity.
  Qed.

  (* ---- c.lui rd, imm6  =  lui rd, sext20(imm6) ---- *)
  Lemma wp_clui_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd : mword 5) (imm6 : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_LUI (imm6, Regidx rd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (luival (sign_extend' 20 imm6))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rd rd rd
              (C_LUI (imm6, Regidx rd)) (UTYPE (sign_extend' 20 imm6, Regidx rd, LUI))
              (luival (sign_extend' 20 imm6)) m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_LUI imm6 (Regidx rd) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc _ _.
    rewrite (exec_execute_UTYPE_LUI_gpr rd (sign_extend' 20 imm6) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity.
  Qed.

  (* ---- c.slli rsd, shamt  =  slli rsd, rsd, shamt ---- *)
  Lemma wp_cslli_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rsd : mword 5) (shamt : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_SLLI (shamt, Regidx rsd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg
        (shift_bits_left (m !!! Regidx rsd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rsd rsd
              (C_SLLI (shamt, Regidx rsd)) (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SLLI))
              (shift_bits_left (m !!! Regidx rsd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_SLLI shamt (Regidx rsd) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_SHIFTIOP_SLLI_gpr rsd rsd shamt s_pc).
    replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_slli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  (* ---- c.srli rsd', shamt  =  srli rsd', rsd', shamt.  rsd = creg2reg_idx crsd ---- *)
  Lemma wp_csrli_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (shamt : mword 6)
      (crsd : cregidx) (rsd : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    creg2reg_idx crsd = Regidx rsd ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_SRLI (shamt, crsd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg
        (shift_bits_right (m !!! Regidx rsd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Hcreg) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rsd rsd
              (C_SRLI (shamt, crsd)) (SHIFTIOP (shamt, Regidx rsd, Regidx rsd, SRLI))
              (shift_bits_right (m !!! Regidx rsd) (subrange_vec_dec shamt (Z.sub log2_xlen 1) 0))
              m pmpcfg0 q HN Hpmp Hrd
              _ _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    - intro s. rewrite (exec_execute_C_SRLI shamt crsd s). rewrite Hcreg. reflexivity.
    - intros s_pc Hnpc Hva _.
      rewrite (exec_execute_SHIFTIOP_SRLI_gpr rsd rsd shamt s_pc).
      replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_srli_val, gpr_src. rewrite Hva. reflexivity.
  Qed.

  (* ---- c.mv rd, rs2  =  add rd, x0, rs2 ---- *)
  Lemma wp_cmv_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rd rs2 : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_MV (Regidx rd, Regidx rs2)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg (m !!! Regidx rs2)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rd rs2 cli_rs1
              (C_MV (Regidx rd, Regidx rs2)) (RTYPE (Regidx rs2, zreg, Regidx rd, ADD))
              (m !!! Regidx rs2) m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_MV (Regidx rd) (Regidx rs2) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx cli_rs1).
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 cli_rs1 rd s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val, cli_rs1.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00"))) 0) with true by (vm_compute; reflexivity).
    rewrite Hva. rewrite add_vec_zero_l. reflexivity.
  Qed.

  (* ---- c.add rsd, rs2  =  add rsd, rsd, rs2 ---- *)
  Lemma wp_cadd_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rsd rs2 : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_ADD (Regidx rsd, Regidx rs2)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg (add_vec (m !!! Regidx rsd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rs2 rsd
              (C_ADD (Regidx rsd, Regidx rs2)) (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, ADD))
              (add_vec (m !!! Regidx rsd) (m !!! Regidx rs2)) m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_ADD (Regidx rsd) (Regidx rs2) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva2 Hvad.
    rewrite (exec_execute_RTYPE_ADD_gpr rs2 rsd rsd s_pc).
    replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_rd_val. rewrite Hva2 Hvad. reflexivity.
  Qed.

  (* ---- c.or rsd', rs2'  =  or rsd', rsd', rs2'.  Both from crsd/crs2 (x8-x15) ---- *)
  Lemma wp_cor_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (crsd crs2 : cregidx) (rsd rs2 : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    creg2reg_idx crsd = Regidx rsd -> creg2reg_idx crs2 = Regidx rs2 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_OR (crsd, crs2)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg (or_vec (m !!! Regidx rsd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Hc1 Hc2) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rs2 rsd
              (C_OR (crsd, crs2)) (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, OR))
              (or_vec (m !!! Regidx rsd) (m !!! Regidx rs2)) m pmpcfg0 q HN Hpmp Hrd
              _ _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    - intro s. rewrite (exec_execute_C_OR crsd crs2 s). rewrite Hc1 Hc2. reflexivity.
    - intros s_pc Hnpc Hva2 Hvad.
      rewrite (exec_execute_RTYPE_OR_gpr rs2 rsd rsd s_pc Hrd).
      unfold gpr_or_val. rewrite Hva2 Hvad. reflexivity.
  Qed.

  (* ---- c.and rsd', rs2'  =  and rsd', rsd', rs2' ---- *)
  Lemma wp_cand_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (crsd crs2 : cregidx) (rsd rs2 : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    creg2reg_idx crsd = Regidx rsd -> creg2reg_idx crs2 = Regidx rs2 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_AND (crsd, crs2)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg (and_vec (m !!! Regidx rsd) (m !!! Regidx rs2))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Hc1 Hc2) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rs2 rsd
              (C_AND (crsd, crs2)) (RTYPE (Regidx rs2, Regidx rsd, Regidx rsd, AND))
              (and_vec (m !!! Regidx rsd) (m !!! Regidx rs2)) m pmpcfg0 q HN Hpmp Hrd
              _ _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    - intro s. rewrite (exec_execute_C_AND crsd crs2 s). rewrite Hc1 Hc2. reflexivity.
    - intros s_pc Hnpc Hva2 Hvad.
      rewrite (exec_execute_RTYPE_AND_gpr rs2 rsd rsd s_pc Hrd).
      unfold gpr_and_val. rewrite Hva2 Hvad. reflexivity.
  Qed.

  (* ---- c.addiw rsd, imm6  =  addiw rsd, rsd, sext(imm6) ---- *)
  Lemma wp_caddiw_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rsd : mword 5) (imm6 : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rsd <> 0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_ADDIW (imm6, Regidx rsd)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rsd := regval_into_reg (sign_extend' 64
        (subrange_vec_dec (add_vec (m !!! Regidx rsd) (sign_extend' 64 imm6)) 31 0))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rsd rsd rsd
              (C_ADDIW (imm6, Regidx rsd)) (ADDIW (sign_extend' 12 imm6, Regidx rsd, Regidx rsd))
              (sign_extend' 64 (subrange_vec_dec
                 (add_vec (m !!! Regidx rsd) (sign_extend' 64 imm6)) 31 0))
              m pmpcfg0 q HN Hpmp Hrd
              (fun s => exec_execute_C_ADDIW imm6 (Regidx rsd) s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    rewrite (exec_execute_ADDIW_gpr rsd rsd (sign_extend' 12 imm6) s_pc).
    replace (Z.eqb (uint rsd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addiw_val. rewrite Hva. rewrite sext6_12_64. reflexivity.
  Qed.

  (* ---- c.addi16sp imm6  =  addi sp, sp, caddi16sp_imm(imm6) ---- *)
  Lemma wp_caddi16sp_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (imm6 : mword 6)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_ADDI16SP imm6) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    assert (Hsp : uint csp_rs1 <> 0) by (vm_compute; discriminate).
    unshelve iApply (wp_rvc_gpr_write E Φ pc csp_rs1 csp_rs1 csp_rs1
              (C_ADDI16SP imm6) (ITYPE (caddi16sp_imm imm6, sp, sp, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm imm6))) m pmpcfg0 q HN Hpmp Hsp
              (fun s => exec_execute_C_ADDI16SP imm6 s) _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change sp with (Regidx csp_rs1).
    rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 csp_rs1 (caddi16sp_imm imm6) s_pc).
    replace (Z.eqb (uint csp_rs1) 0) with false by (symmetry; apply Z.eqb_neq; exact Hsp).
    unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

  (* ---- c.addi4spn rdc, nzimm  =  addi rdc, sp, caddi4spn_imm(nzimm) ---- *)
  Lemma wp_caddi4spn_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (nzimm : mword 8)
      (crdc : cregidx) (rd : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E -> pmp_allows_all pmpcfg0 -> uint rd <> 0 ->
    creg2reg_idx crdc = Regidx rd ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_ADDI4SPN (crdc, nzimm)) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hrd Hcreg) "Hmm Hpmpc Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_rvc_gpr_write E Φ pc rd csp_rs1 csp_rs1
              (C_ADDI4SPN (crdc, nzimm)) (ITYPE (caddi4spn_imm nzimm, sp, Regidx rd, ADDI))
              (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm))) m pmpcfg0 q HN Hpmp Hrd
              _ _
              with "Hmm Hpmpc Hpc Hfile Hinstr Hcont").
    - intro s. rewrite (exec_execute_C_ADDI4SPN crdc nzimm s). rewrite Hcreg. reflexivity.
    - intros s_pc Hnpc Hva _.
      change sp with (Regidx csp_rs1).
      rewrite (exec_execute_ITYPE_ADDI_gpr csp_rs1 rd (caddi4spn_imm nzimm) s_pc).
      replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
      unfold gpr_addi_val. rewrite Hva. reflexivity.
  Qed.

End RvcOps.

(* ===================================================================== *)
(* GENERIC RVC 8-byte LOAD engine.  A compressed load [ci] that            *)
(* [ExecuteAs]-expands to [LOAD (imm, Regidx rs1, Regidx rd, false, 8)];    *)
(* mirrors [wp_ld_gpr] but with [is_rvc = true] / nextPC+2 / the ExecuteAs  *)
(* chain.  Reuses [exec_execute_LOAD_8_gpr] + the identity bridges.         *)
(* ===================================================================== *)
Section RvcLoad.
  Context `{!riscvGS Σ}.

  Lemma wp_rvc_ld_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rd : mword 5)
      (imm : mword 12) (ci : instruction) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dq : dfrac} :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    pmp_all_off pmpcfg0 ->
    uint rd <> 0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    (forall s : mstate,
       exec (execute ci) s = Some (ExecuteAs (LOAD (imm, Regidx rs1, Regidx rd, false, 8)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true ci -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Hrd Halign Hexp.
    iIntros "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & Hread & _).
    iApply (wp_instr E Φ pc true ci pmpcfg0 HN (pmp_all_off_allows_all _ Hpmp) with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) σ with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iAssert (⌜forall j : nat, (N.of_nat j < 8)%N ->
              σ.(mem) !! (pa_add ea j) = Some (nth_byte v j)⌝)%I as %Hbytesf.
    { iIntros (j Hj). assert (Hj' : (j < 8)%nat) by lia.
      iDestruct (big_sepL_lookup _ _ j j with "Hbytes") as "Hbj".
      { rewrite lookup_seq_lt; [reflexivity | exact Hj']. }
      iDestruct (mem_valid with "Hmem Hbj") as %Hmj. iPureIntro. exact Hmj. }
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1).
    { rewrite -Lrs1v. destruct (Z.eqb (uint rs1) 0) eqn:Ez; [reflexivity |].
      unfold s_pc; gpr_trans; reflexivity. }
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_false ea 8 s_pc Lhtifp) as Hwh.
    assert (Hev : extend_value false
              (update_subrange_vec_dec (zeros' (8*1*8)) (8*(0+1)*8-1) (8*0*8) v) = v).
    { unfold extend_value. rewrite sign_extend'_id. apply data2_id. }
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    assert (Hexec_spc :
      exec (execute (LOAD (imm, Regidx rs1, Regidx rd, false, 8))) s_pc
      = Some (RETIRE_SUCCESS,
              set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v))).
    { rewrite -Hev.
      apply (exec_execute_LOAD_8_gpr rs1 rd imm v region s_pc Hrd Lprivp).
      - rewrite Lmsp. exact HMPRV.
      - rewrite Lsecp. exact Hseccfg1.
      - rewrite Ha8. unfold is_aligned_vaddr. unfold is_aligned_paddr in Halign. exact Halign.
      - intro j. rewrite Lpmpcp. exact (proj1 (Hpmp j)).
      - rewrite Lpmap Hpa. exact Hmatch.
      - rewrite Hpa. exact Halign.
      - exact Hread.
      - rewrite Hpa. apply Hwc.
      - rewrite Hpa. apply Hws.
      - rewrite Hpa. apply Hwh.
      - intros j Hj. rewrite Hpa. exact (Hbytesf j Hj). }
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg v) with "Hreg Hrdc")
      as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg v) with "[Hrdc]")
      as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg v)).
    iSplitR.
    { iExists (LOAD (imm, Regidx rs1, Regidx rd, false, 8)). iSplitR.
      - iPureIntro. rewrite Hpceq. fold s_pc. apply Hexp.
      - iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg v)).(sregs)
             = add_vec_int pc 2).
    { unfold s_pc. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- c.ld rdc, uimm(rsc)  (both regs x8-x15) ---- *)
  Lemma wp_cld_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 5)
      (crsc crdc : cregidx) (rs1 rd : mword 5) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E -> pmp_all_off pmpcfg0 -> uint rd <> 0 ->
    creg2reg_idx crsc = Regidx rs1 -> creg2reg_idx crdc = Regidx rd ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_LD (uimm, crsc, crdc)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN Hpmp Hrd Hc1 Hc2 Halign.
    iIntros "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont".
    unshelve iApply (wp_rvc_ld_gpr E Φ pc rs1 rd imm (C_LD (uimm, crsc, crdc)) m v pmpcfg0 q
              HN Hpmp Hrd Halign _ with "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont").
    intro s. rewrite (exec_execute_C_LD uimm crsc crdc s). rewrite Hc1 Hc2. reflexivity.
  Qed.

  (* ---- c.ldsp rd, uimm(sp)  (base = sp) ---- *)
  Lemma wp_cldsp_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rd : mword 5) (m : gmap regidx (mword 64)) (v : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) {dq : dfrac} :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E -> pmp_all_off pmpcfg0 -> uint rd <> 0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_LDSP (uimm, Regidx rd)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg v]> m) -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ{ dq } nth_byte v j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN Hpmp Hrd Halign.
    iIntros "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont".
    unshelve iApply (wp_rvc_ld_gpr E Φ pc csp_rs1 rd imm (C_LDSP (uimm, Regidx rd)) m v pmpcfg0 q
              HN Hpmp Hrd Halign _ with "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont").
    intro s. change sp with (Regidx csp_rs1). apply (exec_execute_C_LDSP uimm (Regidx rd) s).
  Qed.

End RvcLoad.

(* ===================================================================== *)
(* GENERIC RVC 8-byte STORE engine.  A compressed store [ci] that          *)
(* [ExecuteAs]-expands to [STORE (imm, Regidx rs2, Regidx rs1, 8)];         *)
(* mirrors [wp_store_gpr] but with [is_rvc = true] / nextPC+2 / ExecuteAs.  *)
(* Reuses [exec_execute_STORE_8_gpr] + [upd_window_8].                      *)
(* ===================================================================== *)
Section RvcStore.
  Context `{!riscvGS Σ}.

  Lemma wp_rvc_store_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (rs1 rs2 : mword 5)
      (imm : mword 12) (ci : instruction) (m : gmap regidx (mword 64)) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    let offset := sign_extend' 64 imm in
    let ea := add_vec (m !!! Regidx rs1) offset in
    ↑minstretN ⊆ E ->
    pmp_all_off pmpcfg0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    (forall s : mstate,
       exec (execute ci) s = Some (ExecuteAs (STORE (imm, Regidx rs2, Regidx rs1, 8)), s)) ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true ci -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte vold j) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte (m !!! Regidx rs2) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros offset ea HN Hpmp Halign Hexp.
    iIntros "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hbytes Hcont".
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iDestruct "Hmst_k" as (ms0) "(Hms_k & %HmIE & %HMPRV & %HSXL)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np)".
    destruct (Hpma_all ea 8) as (region & Hmatch & _ & _ & Hwrite).
    iApply (wp_instr E Φ pc true ci pmpcfg0 HN (pmp_all_off_allows_all _ Hpmp) with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")   as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms_k")     as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hpmpc_k")   as %Lpmpc.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg")  as %Lsec.
    iDestruct (reg_valid_dq with "Hreg Hpma")      as %Lpma.
    iDestruct (reg_valid_dq with "Hreg Hhtif")     as %Lhtif.
    assert (Hm1 : m !! Regidx rs1 = Some (m !!! Regidx rs1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    assert (Hm2 : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value rs1 (m !!! Regidx rs1) s_pc with "Hreg Hr1c") as %Lrs1v.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm2 with "Hfmap") as "[Hr2c Hfb2]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hr2c") as %Lrs2v.
    iDestruct ("Hfb2" with "Hr2c") as "Hfmap".
    iAssert (⌜addr_is_ram ea⌝)%I as %Hrampa.
    { iDestruct (big_sepL_lookup _ _ 0%nat 0%nat with "Hbytes") as "Hb0".
      { rewrite lookup_seq_lt; [reflexivity | lia]. }
      iDestruct (mem_ram with "Hb0") as %Hr0. rewrite pa_add_0 in Hr0.
      iPureIntro. exact Hr0. }
    assert (Hbase : (if Z.eqb (uint rs1) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                    = m !!! Regidx rs1)
      by exact Lrs1v.
    assert (Hdata : (if Z.eqb (uint rs2) 0 then zero_reg
                     else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs2))) s_pc.(sregs))
                    = m !!! Regidx rs2)
      by exact Lrs2v.
    assert (Lprivp : register_lookup cur_privilege s_pc.(sregs) = Machine)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmsp : register_lookup mstatus s_pc.(sregs) = ms0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lsecp : register_lookup mseccfg s_pc.(sregs) = mseccfg0)
      by (unfold s_pc; tmig; exact Lsec).
    assert (Lpmpcp : register_lookup pmpcfg_n s_pc.(sregs) = pmpcfg0)
      by (unfold s_pc; tmig; exact Lpmpc).
    assert (Lpmap : register_lookup pma_regions s_pc.(sregs) = pmar0)
      by (unfold s_pc; tmig; exact Lpma).
    assert (Lhtifp : register_lookup htif_tohost_base s_pc.(sregs) = None)
      by (unfold s_pc; tmig; exact Lhtif).
    pose proof (within_clint_false ea 8 s_pc (proj1 Hrampa) ltac:(lia)) as Hwc.
    pose proof (within_sig_false ea 8 s_pc (proj2 Hrampa) ltac:(lia)) as Hws.
    pose proof (within_htif_writable_false ea 8 s_pc Lhtifp) as Hwh.
    assert (Ha8 : zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0) = ea).
    { rewrite Hbase. rewrite zero_extend'_id. rewrite subrange_id. reflexivity. }
    assert (Hpa : zero_extend' 64 (add_vec_int (zero_extend' 64 (subrange_vec_dec
              (add_vec (if Z.eqb (uint rs1) 0 then zero_reg
                        else register_lookup (R_bitvector_64 (gpr_of_Z (uint rs1))) s_pc.(sregs))
                       offset) (xlen - 0 - 1) 0)) (0 * 8)) = ea).
    { rewrite Hbase. rewrite !zero_extend'_id. rewrite subrange_id.
      change (0 * 8) with 0. rewrite avi0. reflexivity. }
    pose (s_x := MState s_pc.(sregs) (write_bytes s_pc.(mem) ea 8 (m !!! Regidx rs2))).
    assert (Hexec_spc :
      exec (execute (STORE (imm, Regidx rs2, Regidx rs1, 8))) s_pc
      = Some (RETIRE_SUCCESS, s_x)).
    { rewrite (exec_execute_STORE_8_gpr rs2 rs1 imm region s_pc Lprivp
                ltac:(rewrite Lmsp; exact HMPRV) ltac:(rewrite Lsecp; exact Hseccfg1)
                ltac:(rewrite Ha8; unfold is_aligned_vaddr; unfold is_aligned_paddr in Halign; exact Halign)
                ltac:(intro j; rewrite Lpmpcp; exact (proj1 (Hpmp j)))
                ltac:(rewrite Lpmap Hpa; exact Hmatch) ltac:(rewrite Hpa; exact Halign)
                Hwrite ltac:(rewrite Hpa; apply Hwc) ltac:(rewrite Hpa; apply Hws)
                ltac:(rewrite Hpa; apply Hwh)).
      subst s_x. rewrite Hpa Hdata. reflexivity. }
    iMod (upd_window_8 σ.(mem) ea (m !!! Regidx rs2) vold
            with "Hmem Hbytes") as "[Hmem Hbytes]".
    iModIntro.
    iExists s_x.
    iSplitR.
    { iExists (STORE (imm, Regidx rs2, Regidx rs1, 8)). iSplitR.
      - iPureIntro. rewrite Hpceq. fold s_pc. apply Hexp.
      - iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_x, s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC s_x.(sregs) = add_vec_int pc 2).
    { unfold s_x, s_pc; cbn [sregs]. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hms_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k". iExists ms0. iFrame "Hms_k". iPureIntro. exact (conj HmIE (conj HMPRV HSXL)). }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap] Hbytes").
    iSplitR.
    { iPureIntro. exact Hdom. }
    iExact "Hfmap".
  Qed.

  (* ---- c.sdsp rs2, uimm(sp)  (base = sp, data = rs2) ---- *)
  Lemma wp_csdsp_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (uimm : mword 6)
      (rs2 : mword 5) (m : gmap regidx (mword 64)) (vold : bv 64)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    let imm := zero_extend' 12 (concat_vec uimm ('b"000")) in
    let ea := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 imm) in
    ↑minstretN ⊆ E -> pmp_all_off pmpcfg0 ->
    is_aligned_paddr (Physaddr ea) 8 = true ->
    mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is pc -∗ gpr_file m -∗
    instr pc true (C_SDSP (uimm, Regidx rs2)) -∗
    ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte vold j) -∗
    ( mmode_config (DfracOwn q) -∗ pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗ pc_is (add_vec_int pc 2) -∗
      gpr_file m -∗
      ([∗ list] j ∈ seq 0 8, (pa_add ea j) ↦ₘ nth_byte (m !!! Regidx rs2) j) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros imm ea HN Hpmp Halign.
    iIntros "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont".
    unshelve iApply (wp_rvc_store_gpr E Φ pc csp_rs1 rs2 imm (C_SDSP (uimm, Regidx rs2)) m vold pmpcfg0 q
              HN Hpmp Halign _ with "Hmm Hpmpc Hpc Hfile Hinstr Hbytes Hcont").
    intro s. change sp with (Regidx csp_rs1). apply (exec_execute_C_SDSP uimm (Regidx rs2) s).
  Qed.

End RvcStore.

(* ===================================================================== *)
(* c.ret  =  c.jr ra  =  jalr x0, 0(ra):  a CONTROL-FLOW RVC op.  It        *)
(* ExecuteAs-expands to [JALR (zeros12, Regidx ra, zreg)]; since rd = x0    *)
(* there is NO link write, so the [gpr_file] is UNCHANGED and PC jumps to   *)
(* the target [ (m!!!ra) with low bit cleared ].  Mirrors [wp_jalr_gpr]     *)
(* (the mseccfg.MLPE / Zicfilp check + target alignment), but written with  *)
(* [is_rvc = true] / nextPC+2 / ExecuteAs, and NO destination register.     *)
(* ===================================================================== *)
Section RvcRet.
  Context `{!riscvGS Σ}.

  Definition cret_target (vra : mword 64) : mword 64 :=
    update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0").

  Lemma wp_cret_gpr E (Φ : mval -> iProp Σ) (pc : mword 64) (ra : mword 5)
      (m : gmap regidx (mword 64)) (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :
    ↑minstretN ⊆ E ->
    pmp_allows_all pmpcfg0 ->
    uint ra <> 0 ->
    is_aligned_paddr (Physaddr (cret_target (m !!! Regidx ra))) 4 = true ->
    mmode_config (DfracOwn q) -∗
    pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
    pc_is pc -∗
    gpr_file m -∗
    instr pc true (C_JR (Regidx ra)) -∗
    ( mmode_config (DfracOwn q) -∗
      pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
      pc_is (cret_target (m !!! Regidx ra)) -∗
      gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN Hpmp Hra Halign) "Hmm Hpmpc [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    destruct (aligned4_jump_bits _ Halign) as [Hal0 Hal1].
    iDestruct (mmode_config_split with "Hmm") as "[Hmm_wp Hmm_k]".
    iDestruct "Hmm_k" as "(#Hhw & #Hinv & Hhs_k & Hpriv_k & Hmst_k)".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hmlpe & %Help_np)".
    iDestruct "Hpmpc" as "[Hpmpc_wp Hpmpc_k]".
    iApply (wp_instr E Φ pc true (C_JR (Regidx ra)) pmpcfg0
              HN Hpmp with "Hmm_wp Hpmpc_wp Hpc Hinstr").
    iIntros (σ ns κs nt Hpceq) "Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hm1 : m !! Regidx ra = Some (m !!! Regidx ra))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iDestruct (reg_valid_dq with "Hreg Hpriv_k")  as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmseccfg") as %Lsec.
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hm1 with "Hfmap") as "[Hr1c Hfb1]".
    iDestruct (gpr_pt_value ra (m !!! Regidx ra) s_pc with "Hreg Hr1c") as %Hrv.
    iDestruct ("Hfb1" with "Hr1c") as "Hfmap".
    (* base register at s_pc = m!!!ra (ra <> 0) *)
    assert (Lrav : register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs)
                   = m !!! Regidx ra).
    { rewrite -Hrv. replace (Z.eqb (uint ra) 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hra). reflexivity. }
    (* Zicfilp disabled at s_pc (Machine + MLPE off) *)
    assert (Hzic : exec (currentlyEnabled Ext_Zicfilp) s_pc = Some (false, s_pc)).
    { apply exec_cE_zicfilp_false.
      - unfold s_pc; tmig; exact Lpriv.
      - unfold s_pc; tmig; rewrite Lsec; exact Hmlpe. }
    (* target computed by the model with base at s_pc = cret_target (m!!!ra) *)
    assert (Htgt : update_vec_dec (add_vec
                     (register_lookup (R_bitvector_64 (gpr_of_Z (uint ra))) s_pc.(sregs))
                     (sign_extend' 64 (zeros' 12 : mword 12))) 0 ('b"0")
                   = cret_target (m !!! Regidx ra)).
    { unfold cret_target. rewrite Lrav. reflexivity. }
    assert (Hexec_spc :
      exec (execute (JALR (zeros' 12, Regidx ra, zreg))) s_pc
      = Some (RETIRE_SUCCESS, set_reg s_pc nextPC (cret_target (m !!! Regidx ra)))).
    { change (execute (JALR (zeros' 12, Regidx ra, zreg)))
        with (execute_JALR (zeros' 12) (Regidx ra) zreg).
      change zreg with (Regidx cli_rs1).
      rewrite (exec_execute_JALR_ret (zeros' 12) ra cli_rs1 s_pc Hra
                 ltac:(vm_compute; reflexivity) Hzic
                 ltac:(rewrite Htgt; exact Hal0) ltac:(rewrite Htgt; exact Hal1)).
      rewrite Htgt. reflexivity. }
    (* update nextPC := target so the ghost heap matches s_exec *)
    iMod (reg_update _ nextPC _ (cret_target (m !!! Regidx ra)) with "Hreg Hnpc") as "[Hreg Hnpc]".
    iModIntro.
    iExists (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).
    iSplitR.
    { iExists (JALR (zeros' 12, Regidx ra, zreg)). iSplitR.
      - iPureIntro. rewrite Hpceq. fold s_pc. apply exec_execute_C_JR.
      - iPureIntro. rewrite Hpceq. fold s_pc. exact Hexec_spc. }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hmm' Hpmpc' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc nextPC (cret_target (m !!! Regidx ra))).(sregs)
             = cret_target (m !!! Regidx ra)).
    { rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iAssert (mmode_config (DfracOwn (q/2)))%I
      with "[Hhs_k Hpriv_k Hmst_k]" as "Hmm_k'".
    { iFrame "Hhw Hinv Hhs_k Hpriv_k Hmst_k". }
    iDestruct (mmode_config_combine with "Hmm' Hmm_k'") as "Hmm''".
    iCombine "Hpmpc' Hpmpc_k" as "Hpmpc''".
    iApply ("Hcont" with "Hmm'' Hpmpc'' [$Hpc' $Hnpc] [Hfmap]").
    iSplitR; [ iPureIntro; exact Hdom | iExact "Hfmap" ].
  Qed.

End RvcRet.

(* ===================================================================== *)
(* Demonstration: the register-generic RVC WPs each serve MANY operands.   *)
(* One lemma per compressed op, ANY destination/source register (subject   *)
(* only to the rd<>0 / creg2reg_idx side conditions the model needs).      *)
(* ===================================================================== *)
Section WpGprRvcDemo.
  Context `{!riscvGS Σ}.
  (* c.li a0, imm  and  c.li t0, imm : SAME lemma, different rd. *)
  Definition wp_cli_a0 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm6 : mword 6) :=
    wp_cli_gpr E Φ pc (mword_of_int 10) imm6.
  Definition wp_cli_t0 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) (imm6 : mword 6) :=
    wp_cli_gpr E Φ pc (mword_of_int 5) imm6.
  (* c.mv a0, a1 : rd=a0(x10), rs2=a1(x11). *)
  Definition wp_cmv_a0_a1 (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_cmv_gpr E Φ pc (mword_of_int 10) (mword_of_int 11).
  (* c.ret = c.jr ra : ra = x1. *)
  Definition wp_cret_ra (E : coPset) (Φ : mval -> iProp Σ) (pc : mword 64) :=
    wp_cret_gpr E Φ pc (mword_of_int 1).
  Goal gpr_of_Z (uint (mword_of_int 10 : mword 5)) = x10
    /\ gpr_of_Z (uint (mword_of_int 5 : mword 5)) = x5
    /\ gpr_of_Z (uint (mword_of_int 11 : mword 5)) = x11
    /\ uint (mword_of_int 10 : mword 5) <> 0
    /\ uint (mword_of_int 1 : mword 5) <> 0.
  Proof. repeat split; vm_compute; first [ reflexivity | discriminate ]. Qed.
End WpGprRvcDemo.

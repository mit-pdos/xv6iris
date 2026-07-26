(* WpPopOff.v -- whole-function WP for xv6's pop_off() in S-mode, plus the
   leaves it needs that did not yet exist:

     pop_off @ 0x80000c3a (KernelInstrs.kernel_bytes):
       +0x00 1141      c.addi sp,-16
       +0x02 e406      c.sdsp ra,8(sp)
       +0x04 e022      c.sdsp s0,0(sp)
       +0x06 0800      c.addi4spn s0,sp,16
       +0x08 494500ef  jal ra,mycpu
       +0x0c 100272f3  csrr a5,sstatus
       +0x10 8b89      c.andi a5,2
       +0x12 ef99      c.bnez a5,+0x1e     NOT taken (SIE = 0)
       +0x14 5d3c      c.lw a5,120(a0)     a5 := c->noff
       +0x16 02f05363  blez a5,+0x26       NOT taken (noff >= 1)
       +0x1a 37fd      c.addiw a5,-1
       +0x1c dd3c      c.sw a5,120(a0)     c->noff := noff-1
       +0x1e e789      c.bnez a5,+0xa      taken iff noff-1 <> 0
       +0x20 5d7c      c.lw a5,124(a0)     a5 := c->intena  (only if noff-1 = 0)
       +0x22 c399      c.beqz a5,+0x6      taken (intena = 0)
       +0x28 60a2 / +0x2a 6402 / +0x2c 0141 / +0x2e 8082   epilogue

   New leaves: [wp_cbeqz_fall_s_raw_pt] (c.beqz fall-through), [wp_bge_x0_fall_s_pt]
   (32-bit blez not-taken), [wp_fence_s_pt] (fence rw,w -- release() needs it;
   defined here with the rest of the new leaf kit), [wp_csrr_sstatus_s_pt]
   (read-only csrr of sstatus). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
(* QUALIFIED (no Import): sstatus SIE-bit bridges for the pop_off interrupt-off fact. *)
Require WpGprCsrwC.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore WpMemsetS.
Require Import WpPushOffCsr.
Require Import WpRvcBridge KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode lemmas.                                                         *)
(* ===================================================================== *)

Local Ltac pp_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac pp_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  pp_ast.

(* +0x08  0x495000ef  jal ra,mycpu (offset +0xc94) *)
Lemma ppdec_jal_mycpu s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x495000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pp_dbase s Hpriv ]. Qed.

(* +0x0c  0x100027f3  csrr a5,sstatus  (csrrs a5,sstatus,x0) *)
Lemma ppdec_csrr s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x100027f3 : mword 32)) s
  = Some (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pp_dbase s Hpriv ]. Qed.

(* +0x16  0x02f05363  blez a5,+0x26  (bge x0,a5) *)
Lemma ppdec_blez s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f05363 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pp_dbase s Hpriv ]. Qed.

(* release +0x16  0x0310000f  fence rw,w *)
Lemma ppdec_fence s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0310000f : mword 32)) s
  = Some (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                 Regidx (mword_of_int 0), Regidx (mword_of_int 0)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pp_dbase s Hpriv ]. Qed.

(* +0x12  0xef99  c.bnez a5,+0x1e *)
Lemma ppdec_bnez1e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef99 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 15, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1e  0xe789  c.bnez a5,+0xa *)
Lemma ppdec_bnez0a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe789 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 5, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x22  0xc399  c.beqz a5,+0x6 *)
Lemma ppdec_beqz06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc399 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 3, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* release +0x10  0xcd11  c.beqz a0,+0x1c *)
Lemma ppdec_beqz1c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd11 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 14, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x1a  0x37fd  c.addiw a5,-1 *)
Lemma ppdec_addiwm1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x37fd : mword 16)) s
  = Some (C_ADDIW (mword_of_int 63, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x20  0x5d7c  c.lw a5,124(a0) *)
Lemma ppdec_lw124 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5d7c : mword 16)) s
  = Some (C_LW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- compressed-AST expansions ---- *)

Lemma ppexec_lw124 s :
  exec (execute (C_LW (mword_of_int 31, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 124, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_LW. cbn zeta.
  rewrite exec_returnM. rewrite po_cr2. rewrite po_cr7.
  pp_ast.
Qed.

Lemma ppexec_andi2 s :
  exec (execute (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_ANDI. cbn zeta.
  rewrite exec_returnM. rewrite !po_cr7. pp_ast.
Qed.

(* ===================================================================== *)
(* BGE fall-through execute.                                              *)
(* ===================================================================== *)



(* ===================================================================== *)
(* FENCE rw,w execute (a no-op barrier at Supervisor with FIOM = 0).      *)
(* ===================================================================== *)




(* ===================================================================== *)
(* Read-only csrr rd,sstatus (CSRRS with rs1 = x0: no write happens).     *)
(* ===================================================================== *)

Lemma exec_csr_id_read_callback_sstatus (d : mword 64) s :
  exec (csr_id_read_callback csr_sstatus d) s = Some (tt, s).
Proof.
  assert (H : csr_id_read_callback csr_sstatus d = returnM tt) by (vm_compute; reflexivity).
  rewrite H. apply exec_returnM.
Qed.

Lemma exec_execute_csrr_sstatus (rd : mword 5) (m : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup mstatus s.(sregs) = m ->
  eq_vec (_get_Misa_S (register_lookup misa s.(sregs))) ('b"1") = true ->
  uint rd <> 0 ->
  exec (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))) s
    = Some (RETIRE_SUCCESS,
            set_reg s (R_bitvector_64 (gpr_of_Z (uint rd))) (regval_into_reg (sstatus_read m))).
Proof.
  intros Hpriv Hm HS Hrd.
  change (execute (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)))
    with (execute_CSRReg csr_sstatus (Regidx (mword_of_int 0)) (Regidx rd) CSRRS).
  unfold execute_CSRReg.
  (* access_type = csr_access_type CSRRS _ true = CSRRead *)
  replace (generic_eq (Regidx (mword_of_int 0 : mword 5)) zreg) with true
    by (vm_compute; reflexivity).
  cbn zeta.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr (mword_of_int 0) s)).
  unfold doCSR.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_check_CSR_result_sstatus_S s HS)). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)). rewrite Hpriv.
  unfold ext_check_CSR. cbn match.
  replace (generic_neq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRWrite)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_CSR_sstatus s)). rewrite Hm.
  replace (eq_vec csr_sstatus (Ox"344")) with false by (vm_compute; reflexivity).
  replace (eq_vec csr_sstatus (Ox"144")) with false by (vm_compute; reflexivity). cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_returnM (sstatus_read m) s)).
  replace (generic_eq (csr_access_type CSRRS (generic_eq (Regidx rd) zreg) true) CSRRead)
    with true by (vm_compute; reflexivity).
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_csr_id_read_callback_sstatus (sstatus_read m) s)).
  assert (HwX : exec (wX_bits (Regidx rd) (sstatus_read m)) s
                = Some (tt, set_reg s (R_bitvector_64 (gpr_of_Z (uint rd)))
                              (regval_into_reg (sstatus_read m)))).
  { rewrite (exec_wX_bits_gpr rd _ s).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    reflexivity. }
  rewrite (exec_bind0_Some _ _ _ _ _ HwX).
  apply exec_returnM.
Qed.

(* ===================================================================== *)
(* New WP leaves.                                                         *)
(* ===================================================================== *)
Section WpPopOffLeaves.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- c.beqz rs',imm8 FALL-THROUGH (register nonzero) ---- *)

  (* ---- 32-bit bge x0,rs2 (blez rs2) FALL-THROUGH: rs2 signed-positive ---- *)

  (* ---- fence rw,w: a pure no-op step (Supervisor, FIOM = 0) ---- *)

  (* ---- csrr rd,sstatus (read-only CSRRS with rs1 = x0) ---- *)

End WpPopOffLeaves.

(* ===================================================================== *)
(* [instr] facts for pop_off's instructions from [kernel_text].           *)
(* ===================================================================== *)
Section WpPopOffInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PP := KernelSyms.pop_off.

  Lemma ppi_00 : kernel_text -∗ instr (mword_of_int (PP + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PP + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (PP + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma ppi_02 : kernel_text -∗ instr (mword_of_int (PP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PP + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma ppi_04 : kernel_text -∗ instr (mword_of_int (PP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PP + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma ppi_06 : kernel_text -∗ instr (mword_of_int (PP + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PP + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PP + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma ppi_08 : kernel_text -∗ instr (mword_of_int (PP + 0x08) : mword 64) false (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PP + 0x08)%Z (mword_of_int 0x495000ef : mword 32)
    (mword_of_int (PP + 0x08) : mword 64) (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))) ppdec_jal_mycpu. Qed.

  Lemma ppi_0c : kernel_text -∗ instr (mword_of_int (PP + 0x0c) : mword 64) false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)).
  Proof. mk_base (PP + 0x0c)%Z (mword_of_int 0x100027f3 : mword 32)
    (mword_of_int (PP + 0x0c) : mword 64) (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)) ppdec_csrr. Qed.

  Lemma ppi_10 : kernel_text -∗ instr (mword_of_int (PP + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (PP + 0x10)%Z (mword_of_int 0x8b89 : mword 16)
    (mword_of_int (PP + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) cdec_8b89 ppexec_andi2. Qed.

  Lemma ppi_12 : kernel_text -∗ instr (mword_of_int (PP + 0x12) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (PP + 0x12)%Z (mword_of_int 0xef99 : mword 16)
    (mword_of_int (PP + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ppdec_bnez1e exec_execute_C_BNEZ. Qed.

  Lemma ppi_14 : kernel_text -∗ instr (mword_of_int (PP + 0x14) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PP + 0x14)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PP + 0x14) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) cdec_5d3c poexec_lw. Qed.

  Lemma ppi_16 : kernel_text -∗ instr (mword_of_int (PP + 0x16) : mword 64) false (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PP + 0x16)%Z (mword_of_int 0x02f05363 : mword 32)
    (mword_of_int (PP + 0x16) : mword 64) (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) ppdec_blez. Qed.

  Lemma ppi_1a : kernel_text -∗ instr (mword_of_int (PP + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (PP + 0x1a)%Z (mword_of_int 0x37fd : mword 16)
    (mword_of_int (PP + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) ppdec_addiwm1 exec_execute_C_ADDIW. Qed.

  Lemma ppi_1c : kernel_text -∗ instr (mword_of_int (PP + 0x1c) : mword 64) true (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PP + 0x1c)%Z (mword_of_int 0xdd3c : mword 16)
    (mword_of_int (PP + 0x1c) : mword 64) (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) cdec_dd3c poexec_sw120. Qed.

  Lemma ppi_1e : kernel_text -∗ instr (mword_of_int (PP + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (PP + 0x1e)%Z (mword_of_int 0xe789 : mword 16)
    (mword_of_int (PP + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ppdec_bnez0a exec_execute_C_BNEZ. Qed.

  Lemma ppi_20 : kernel_text -∗ instr (mword_of_int (PP + 0x20) : mword 64) true (LOAD (mword_of_int 124, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PP + 0x20)%Z (mword_of_int 0x5d7c : mword 16)
    (mword_of_int (PP + 0x20) : mword 64) (LOAD (mword_of_int 124, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) ppdec_lw124 ppexec_lw124. Qed.

  Lemma ppi_22 : kernel_text -∗ instr (mword_of_int (PP + 0x22) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PP + 0x22)%Z (mword_of_int 0xc399 : mword 16)
    (mword_of_int (PP + 0x22) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) ppdec_beqz06 exec_execute_C_BEQZ. Qed.

  Lemma ppi_28 : kernel_text -∗ instr (mword_of_int (PP + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PP + 0x28)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PP + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma ppi_2a : kernel_text -∗ instr (mword_of_int (PP + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PP + 0x2a)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PP + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma ppi_2c : kernel_text -∗ instr (mword_of_int (PP + 0x2c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PP + 0x2c)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PP + 0x2c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma ppi_2e : kernel_text -∗ instr (mword_of_int (PP + 0x2e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PP + 0x2e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PP + 0x2e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpPopOffInstr.

(* BEQ-taken tolerating a bit1 = 1 target under Zca (twin of
   WpMemsetS.exec_execute_BTYPE_BNE_taken_zca). *)

(* c.bnez / c.beqz TAKEN with only 2-aligned targets (Zca from hw_config). *)
Section WpPopOffTakenZca.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.



End WpPopOffTakenZca.


(* ===================================================================== *)
(* wp_pop_off -- S-mode whole-function WP for pop_off().                  *)
(* Preconditions (beyond the standard S-mode config): interrupts are OFF  *)
(* (mstatus.SIE = 0, via the [Hsst2] premise on the sstatus view), the    *)
(* per-cpu noff is signed-POSITIVE, and the saved intena is 0 (so the     *)
(* csrsi that would re-enable interrupts is provably skipped).            *)
(* ===================================================================== *)
(* SIE=0 (folded into smode_config) gives pop_off's interrupt-off fact
   [sstatus & 2 = 0] with mstatus0 hidden.  [mword1_zero_of_ne_one] is the
   shared pure bitvector fact (RiscvExtras). *)
Lemma pop_sstatus_clear_neq (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  neq_vec (and_vec (sstatus_read m)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof.
  intro HSIE.
  unfold neq_vec. apply negb_false_iff. apply eq_vec_true_iff.
  assert (Hz : _get_Mstatus_SIE m = ('b"0" : mword 1))
    by (apply mword1_zero_of_ne_one; exact HSIE).
  assert (Hb1 : Z.testbit (bv_unsigned (sstatus_read m)) 1 = false).
  { unfold sstatus_read. rewrite WpGprCsrwC.subrange_full.
    apply WpGprCsrwC.sie_bit. rewrite WpGprCsrwC.mSIE_lower. exact Hz. }
  assert (Hmask : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)) : mword 64) = 2)
    by (vm_compute; reflexivity).
  assert (Hzr : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  apply bv_eq. rewrite WpGprCsrwC.and_vec_unsigned. rewrite Hmask. rewrite Hzr.
  apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (decide (j = 1)) as [->|Hne].
  - rewrite Hb1. reflexivity.
  - assert (Ht2 : Z.testbit 2 j = false).
    { destruct (Z.eq_dec j 0) as [->|Hj0].
      - reflexivity.
      - apply Z.bits_above_log2; [lia|]. change (Z.log2 2) with 1. lia. }
    rewrite Ht2. apply andb_false_r.
Qed.

(* ===================================================================== *)
(* S-mode VCgen blocks for pop_off's straight-line runs (VcGenS.v).       *)
(*                                                                        *)
(* pop_off's blocks use PARTIAL symbolic register maps (the agreement     *)
(* interface): each block's map seeds only the registers it touches plus  *)
(* the ones whose values must be carried across it (s1/tp/a0 feed the     *)
(* final register facts; sp feeds the epilogue).  Variable convention:    *)
(* xk ↦ SX k 0 (the register's current value); 33/34 = memory-cell        *)
(* contents. *)


(* the noff word cell: [a0 + 120], variable 33 = the (sign-extended)
   pre-decrement word. *)


(* [c.addiw a5,-1; c.sw a5,120(a0)]: the decrement is tracked symbolically
   in the 32-bit domain -- a5 and the stored word become "noff minus one"
   ([SX32 33 (2^32-1)]). *)




Section WpPopOffTopSec.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Notation PP := KernelSyms.pop_off.



  (* ------------------------------------------------------------------ *)
  (* the call composite (jal + the whole mycpu): the WpPushOffTop proof,  *)
  (* verbatim, with wp_mycpu as the callee.                            *)
  (* ------------------------------------------------------------------ *)


  (* [smode_config] view of the pure sstatus read (csrrs rd,sstatus,x0): mstatus
     is untouched, and the value read into [rd] is exposed only through the ghost
     SIE flag as [sstatus_read ms] for SOME ms with SIE=0 (mirror of
     [wp_csrrci_sstatus_scfg_pt]). *)

  (* ---- [smode_config] leaf wrappers used by [wp_pop_off]: each unbundles the
     bundle, calls the raw S-mode leaf, and rebundles.  The non-config side
     conditions stay explicit; every S-mode config fact comes from the bundle. ---- *)







  (* [wp_cret_s_zca_scfg_pt] (the c.ret S-mode leaf) lives in WpSmodeJalr; used
     here via that import.  (Formerly duplicated in this file.) *)

  (* [smode_config] view of the mycpu() VCgen callee: the raw callee needs full
     config cells + the SIE ghost half, so unbundle here and rebundle on return
     (pop_off's post is existential, so re-pinning a value is fine). *)






End WpPopOffTopSec.

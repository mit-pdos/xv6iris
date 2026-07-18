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

   New leaves: [wp_cbeqz_fall_s_raw] (c.beqz fall-through), [wp_bge_x0_fall_s]
   (32-bit blez not-taken), [wp_fence_s] (fence rw,w -- release() needs it;
   defined here with the rest of the new leaf kit), [wp_csrr_sstatus_s]
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
Require Import MinstretInv InstrBytes.
Require Import WpDecode KernelText.
Require Import WpGpr.
Require Import WpMmodeLeafBase.
Require Import SmodeCore WpMemsetS WpKernelvecNew.
Require Import WpSmodeBtype.
Require Import WpSmodeCsr.
Require Import WpSmodeItype.
Require Import WpSmodeJalr.
Require Import WpSmodeLoad.
Require Import WpPushOffCsr WpMycpu WpMemsetInstr.
Require Import WpSmodeBtype.
Require Import WpSmodeLoad.
Require Import StackOwn.
Require Import CalleeSaved.
Require Import WpRvcBridge KernelRvcDecode.
Require Import VcGen VcGenS.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase WpSmodeAddiw WpSmodeShiftiop WpSmodeRtype WpSmodeItype WpSmodeJal WpSmodeJalr WpSmodeCsr WpSmodeLoad WpSmodeStore WpSmodeBtype.
Require Export WpSmodeFence.
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

(* +0x10  0x8b89  c.andi a5,2 *)
Lemma ppdec_andi s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b89 : mword 16)) s
  = Some (C_ANDI (mword_of_int 2, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

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

Lemma exec_BTYPE_cmp_BGE (rs2 rs1 : mword 5) s :
  exec (Defs.bind (rX_bits (Regidx rs1))
          (fun w2 => Defs.bind (rX_bits (Regidx rs2))
             (fun w3 => returnM (zopz0zKzJ_s w2 w3)))) s
    = Some (zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s), s).
Proof.
  unfold rvv.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs1 s)).
  rewrite (exec_bind_Some _ _ _ _ _ (exec_rX_bits_gpr rs2 s)).
  apply exec_returnM.
Qed.

Lemma exec_execute_BTYPE_BGE_fall (imm : mword 13) (rs2 rs1 : mword 5) s :
  zopz0zKzJ_s (rvv rs1 s) (rvv rs2 s) = false ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BGE))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intro Hfall.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BGE rs2 rs1 s)).
  rewrite Hfall. apply exec_returnM.
Qed.

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
    (mword_of_int (PP + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma ppi_02 : kernel_text -∗ instr (mword_of_int (PP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PP + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma ppi_04 : kernel_text -∗ instr (mword_of_int (PP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PP + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma ppi_06 : kernel_text -∗ instr (mword_of_int (PP + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PP + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PP + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma ppi_08 : kernel_text -∗ instr (mword_of_int (PP + 0x08) : mword 64) false (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PP + 0x08)%Z (mword_of_int 0x495000ef : mword 32)
    (mword_of_int (PP + 0x08) : mword 64) (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))) ppdec_jal_mycpu. Qed.

  Lemma ppi_0c : kernel_text -∗ instr (mword_of_int (PP + 0x0c) : mword 64) false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)).
  Proof. mk_base (PP + 0x0c)%Z (mword_of_int 0x100027f3 : mword 32)
    (mword_of_int (PP + 0x0c) : mword 64) (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)) ppdec_csrr. Qed.

  Lemma ppi_10 : kernel_text -∗ instr (mword_of_int (PP + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc (PP + 0x10)%Z (mword_of_int 0x8b89 : mword 16)
    (mword_of_int (PP + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) ppdec_andi ppexec_andi2. Qed.

  Lemma ppi_12 : kernel_text -∗ instr (mword_of_int (PP + 0x12) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (PP + 0x12)%Z (mword_of_int 0xef99 : mword 16)
    (mword_of_int (PP + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ppdec_bnez1e exec_execute_C_BNEZ. Qed.

  Lemma ppi_14 : kernel_text -∗ instr (mword_of_int (PP + 0x14) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (PP + 0x14)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PP + 0x14) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) podec_lw poexec_lw. Qed.

  Lemma ppi_16 : kernel_text -∗ instr (mword_of_int (PP + 0x16) : mword 64) false (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PP + 0x16)%Z (mword_of_int 0x02f05363 : mword 32)
    (mword_of_int (PP + 0x16) : mword 64) (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) ppdec_blez. Qed.

  Lemma ppi_1a : kernel_text -∗ instr (mword_of_int (PP + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (PP + 0x1a)%Z (mword_of_int 0x37fd : mword 16)
    (mword_of_int (PP + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) ppdec_addiwm1 exec_execute_C_ADDIW. Qed.

  Lemma ppi_1c : kernel_text -∗ instr (mword_of_int (PP + 0x1c) : mword 64) true (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (PP + 0x1c)%Z (mword_of_int 0xdd3c : mword 16)
    (mword_of_int (PP + 0x1c) : mword 64) (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) podec_sw120 poexec_sw120. Qed.

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
    (mword_of_int (PP + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma ppi_2a : kernel_text -∗ instr (mword_of_int (PP + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PP + 0x2a)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PP + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma ppi_2c : kernel_text -∗ instr (mword_of_int (PP + 0x2c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PP + 0x2c)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PP + 0x2c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma ppi_2e : kernel_text -∗ instr (mword_of_int (PP + 0x2e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PP + 0x2e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PP + 0x2e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

End WpPopOffInstr.

(* BEQ-taken tolerating a bit1 = 1 target under Zca (twin of
   WpMemsetS.exec_execute_BTYPE_BNE_taken_zca). *)
Lemma exec_execute_BTYPE_BEQ_taken_zca (imm : mword 13) (rs2 rs1 : mword 5) s :
  eq_vec (rvv rs1 s) (rvv rs2 s) = true ->
  eq_vec (access_vec_dec (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm)) 0) ('b"0") = true ->
  exec (currentlyEnabled Ext_Zca) s = Some (true, s) ->
  exec (execute (BTYPE (imm, Regidx rs2, Regidx rs1, BEQ))) s
    = Some (RETIRE_SUCCESS,
            set_reg s nextPC (add_vec (register_lookup PC s.(sregs)) (sign_extend' 64 imm))).
Proof.
  intros Htaken Halign Hzca.
  unfold execute. cbn match. unfold execute_BTYPE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_BTYPE_cmp_BEQ rs2 rs1 s)).
  rewrite Htaken.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg PC s)).
  exact (exec_jump_to_zca _ s Halign Hzca).
Qed.

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

Section WpPopOffTopSec.
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
  (* verbatim, with wp_mycpu as the callee.                            *)
  (* ------------------------------------------------------------------ *)
  Lemma wp_call_mycpu_vc (root_ppn : mword 44) (γc : gname) (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      :
    let ra_idx : mword 5 := mword_of_int 1 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let ra0 := m0 !!! Regidx ra_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    add_vec P (sign_extend' 64 jimm) = pcE ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_Mstatus_MXR mstatus0) ('b"0") = true ->
    pmm_mode_backwards (_get_MEnvcfg_PMM menvcfg0) = PMM_Disabled ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    menvcfg0 = MENVCFG_S ->
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
    stack_own (m0 !!! Regidx csp_rs1) 2 -∗
    ( ∀ mo,
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ Supervisor -∗ mstatus ↦ᵣ mstatus0 -∗
      ghost_var γc (1/2) (_get_Mstatus_SIE mstatus0) -∗
      mie ↦ᵣ mie_v -∗ mideleg ↦ᵣ mdv0 -∗ menvcfg ↦ᵣ menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mo -∗
      ⌜ callee_saved m mo /\
        mo !!! Regidx (mword_of_int 10 : mword 5)
          = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ⌝ -∗
      stack_own (m0 !!! Regidx csp_rs1) 2 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ra_idx m0 pcE ra0 ret_tgt Htarget Halign_tgt HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe HFIOM Hlegal Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv #Htext Hpc Hfile Hjal Hstk Hcont".
    iDestruct (kv_cfg_split γc mstatus0 mie_v mdv0 menvcfg0 HSIE HMPRV HSXL HMXR Hlegal Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv")
      as "(Hsm & Hhs2 & Hpriv2 & Hms2 & Hmie2 & Hmdl2 & Hmenv2)".
    iApply (wp_jal_gpr_s2 root_ppn γc Φ P (mword_of_int 1) jimm m (1/2)%Qp
 ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halign_tgt)
              with "Hsm Htlbinv Hpc Hfile Hjal [-]").
    iIntros "Hsm Htlbinv Hpc Hfile".
    iEval (rewrite Htarget) in "Hpc".
    iDestruct (kv_cfg_recombine γc mstatus0 mie_v mdv0 menvcfg0
                 with "Hsm Hhs2 Hpriv2 Hms2 Hmie2 Hmdl2 Hmenv2")
      as "(Hhs & Hpriv & Hms & Hgc & Hmie & Hmdl & Hmenv)".
    iApply (wp_mycpu root_ppn Φ m0 2 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              ltac:(lia) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hstk [Hgc Hcont]").
    iIntros (mo) "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile %Hmcs Hstk".
    iApply ("Hcont" $! mo with
              "Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Hpc Hfile [%] Hstk").
    destruct Hmcs as [Hcs Ha0]. split.
    - exact (callee_saved_insert_ra _ _ _ Hcs).
    - assert (Htp : m0 !!! Regidx (mword_of_int 4 : mword 5)
                    = m !!! Regidx (mword_of_int 4 : mword 5))
        by (rewrite /m0 lookup_total_insert_ne; [ reflexivity | vm_compute; discriminate ]).
      rewrite -Htp. exact Ha0.
  Qed.

  (* [smode_config] view of the pure sstatus read (csrrs rd,sstatus,x0): mstatus
     is untouched, and the value read into [rd] is exposed only through the ghost
     SIE flag as [sstatus_read ms] for SOME ms with SIE=0 (mirror of
     [wp_csrrci_sstatus_scfg]). *)

  (* ---- [smode_config] leaf wrappers used by [wp_pop_off]: each unbundles the
     bundle, calls the raw S-mode leaf, and rebundles.  The non-config side
     conditions stay explicit; every S-mode config fact comes from the bundle. ---- *)







  (* [wp_cret_s_zca_scfg] (the c.ret S-mode leaf) lives in WpSmodeJalr; used
     here via that import.  (Formerly duplicated in this file.) *)

  (* [smode_config] view of the mycpu() VCgen callee: the raw callee needs full
     config cells + the SIE ghost half, so unbundle here and rebundle on return
     (pop_off's post is existential, so re-pinning a value is fine). *)
  Lemma wp_call_mycpu_vc_scfg (root_ppn : mword 44) (γc : gname) (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : gmap regidx (mword 64))
      :
    let ra_idx : mword 5 := mword_of_int 1 in
    let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
    let pcE := mword_of_int KernelSyms.mycpu in
    let ra0 := m0 !!! Regidx ra_idx in
    let ret_tgt := update_vec_dec (add_vec ra0 (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    add_vec P (sign_extend' 64 jimm) = pcE ->
    eq_vec (access_vec_dec pcE 0) ('b"0") = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is P -∗ gpr_file m -∗
    instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
    stack_own (m0 !!! Regidx csp_rs1) 2 -∗
    ( ∀ mo,
      smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mo -∗
      ⌜ callee_saved m mo /\
        mo !!! Regidx (mword_of_int 10 : mword 5)
          = mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) ⌝ -∗
      stack_own (m0 !!! Regidx csp_rs1) 2 -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros ra_idx m0 pcE ra0 ret_tgt Htarget Halign_tgt Hal0.
    iIntros "Hcfg Htlbinv Htext Hpc Hfile Hjal Hstk Hcont".
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(Hhw & Hinv & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hhw" as "#Hhw". iDestruct "Hinv" as "#Hinv".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hlegal)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %HFIOM & %Hmenvval0)".
    iApply (wp_call_mycpu_vc root_ppn γc Φ P jimm m
              mstatus0 mie_v mdv0 menvcfg0
 Htarget Halign_tgt
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval0 Hlpe HFIOM Hlegal Hal0
              with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Htext Hpc Hfile Hjal Hstk [-]").
    iIntros (mo) "Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv Htlbinv Hpc Hfile %Hmc Hstk".
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hlegal Hmm HPBMTE Hpmm Hlpe HFIOM Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
    iApply ("Hcont" $! mo with "Hcfg Htlbinv Hpc Hfile [%] Hstk").
    exact Hmc.
  Qed.

  Lemma wp_pop_off (root_ppn : mword 44) (γc : gname) (Φ : mval -> iProp Σ)
      (m : gmap regidx (mword 64))
      (noffv intenav : mword 32)
      (n : nat)
      {dqi : dfrac} :
    let pcE : mword 64 := mword_of_int PP in
    let a0v := mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) in
    let a_noff := add_vec a0v (sign_extend' 64 (mword_of_int 120 : mword 12)) in
    let a_int := add_vec a0v (sign_extend' 64 (mword_of_int 124 : mword 12)) in
    let nv1 := sign_extend' 64 (subrange_vec_dec (add_vec (sign_extend' 64 noffv) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0) in
    let storeval := (autocast (T := mword) (subrange_vec_dec nv1 (Z.sub (Z.mul 4 8) 1) 0) : mword 32) in
    let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    (4 ≤ n)%nat ->
    (* S-mode config facts + the interrupt-off sstatus fact are folded into
       [smode_config γc] below. *)
    (* noff >= 1 (signed) *)
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    (* saved intena is 0 *)
    eq_vec (sign_extend' 64 intenav) zero_reg = true ->
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗
    tlb_inv root_ppn -∗
    kernel_text -∗ pc_is pcE -∗ gpr_file m -∗
    (* pop_off's whole 4-slot frame (2 own p8/p0 + 2 mycpu) as
       [stack_own (m!!!csp) n] (n>=4). *)
    stack_own (m !!! Regidx csp_rs1) n -∗
    a_noff ↦₄ noffv -∗
    a_int ↦₄{ dqi } intenav -∗
    ( ∀ mf,
      smode_config γc (DfracOwn 1) -∗
      tlb_inv root_ppn -∗
      pc_is ret_tgt -∗
      gpr_file mf -∗
      ⌜ callee_saved m mf ⌝ -∗
      a_noff ↦₄ storeval -∗
      a_int ↦₄{ dqi } intenav -∗
      stack_own (m !!! Regidx csp_rs1) n -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}.
  Proof.
    intros pcE a0v a_noff a_int nv1 storeval ret_tgt Hn4 Hnoffpos Hint Hal0.
    set (spd := add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))).
    set (a_p8 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000")))).
    set (a_p0 := add_vec spd (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000")))).
    iIntros "Hcfg Htlbinv
             #Htext Hpc Hfile Hframe Hnoff Hint Hcont".
    (* peel the 2 own slots as cells; keep mycpu's 2-slot frame as a
       [stack_own] slice the body threads directly. *)
    iDestruct (stack_own_split_1 (m !!! Regidx csp_rs1) 4 n ltac:(lia) with "Hframe") as "[Htop Hdeep]".
    iDestruct (stack_own_split_1 (m !!! Regidx csp_rs1) 2 4 ltac:(lia) with "Htop") as "[Ht12 Hstk]".
    iDestruct (stack_own_2_elim with "Ht12") as (vp8 vp0) "[Hp8 Hp0]".
    assert (Hb1 : a_p8 = pa_stk (m !!! Regidx csp_rs1) 1).
    { rewrite /a_p8 /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : a_p0 = pa_stk (m !!! Regidx csp_rs1) 2).
    { rewrite /a_p0 /spd. unfold pa_stk, add_vec_int. rewrite !pa_stk_off2. f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hspd2 : pa_stk (m !!! Regidx csp_rs1) 2 = spd).
    { rewrite /spd. unfold pa_stk, add_vec_int. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite -Hb1) in "Hp8". iEval (rewrite -Hb2) in "Hp0".
    iEval (rewrite Hspd2) in "Hstk".
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
    iApply (wp_vc_block_s root_ppn mycpu_prologue Φ
              (VSt PP po_pro_regs0 mycpu_pro_heap0 [])
              (VSt (PP + 8) po_pro_regs1 mycpu_pro_heap1 [])
              ρA m γc
              (dq:=DfracOwn 1)
 po_prologue_run HmA
              with "Hcfg Htlbinv
                    Hpc Hfile Hbi [Hp8 Hp0] []").
    { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_pro_heap0.
      cbn [big_opL fst snd]. rewrite Hara Has0 Hv33 Hv34.
      iFrame "Hp8 Hp0". }
    { rewrite /vheap4_own. cbn [vheap4]. done. }
    iIntros (M1) "%HmA1 Hcfg Htlbinv Hpc Hfile Hheap _".
    destruct HmA1 as [HmA1 HaA1].
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
    (* +0x08 jal ra,mycpu; the callee needs raw config cells + the SIE ghost, so
       unbundle here and rebundle when it returns (pop_off's post is existential,
       so re-pinning a value is fine). *)
    iApply (wp_call_mycpu_vc_scfg root_ppn γc Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) M1
 ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(rewrite lookup_total_insert; vm_compute; reflexivity)
              with "Hcfg Htlbinv Htext Hpc Hfile Hi08 [Hstk] [-]").
    { iEval (rewrite HspP2r). iExact "Hstk". }
    iIntros (C) "Hcfg Htlbinv Hpc Hfile %Hmc Hstk".
    iEval (rewrite HspP2r) in "Hstk".
    iEval (rewrite lookup_total_insert) in "Hpc".
    assert (Hpc0c : update_vec_dec (add_vec (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                    = (mword_of_int (PP + 0x0c) : mword 64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc0c) in "Hpc".
    destruct Hmc as (Hmc_cs & Hmc_a0).
    unfold callee_saved in Hmc_cs.
    destruct Hmc_cs as (Hmc_csp & Hmc_tp & Hmc_s0 & Hmc_s1 & Hmc_s2 & Hmc_s3 & Hmc_s4 & Hmc_s5 & Hmc_s6 & Hmc_s7 & Hmc_s8 & Hmc_s9 & Hmc_s10 & Hmc_s11).
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite Hmc_a0 Htp1. reflexivity. }
    assert (HspC : C !!! Regidx csp_rs1 = spd).
    { rewrite Hmc_csp. exact Hsp1. }
    assert (Hs9C : C !!! Regidx (mword_of_int 9 : mword 5)
                   = m !!! Regidx (mword_of_int 9 : mword 5)).
    { rewrite Hmc_s1. exact Hs91. }
    assert (HtpC : C !!! Regidx (mword_of_int 4 : mword 5)
                   = m !!! Regidx (mword_of_int 4 : mword 5)).
    { rewrite Hmc_tp. exact Htp1. }
    (* +0x0c csrr a5,sstatus: read via the SIE ghost.  Yields [sstatus_read msr]
       for SOME [msr] with SIE = 0 (the concrete mstatus stays hidden in the
       bundle).  [msr] is contained to +0x0c..+0x12: a5 is overwritten at +0x14. *)
    iApply (wp_csrr_sstatus_scfg root_ppn γc Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15) C (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hcfg Htlbinv Hpc Hfileex".
    iDestruct "Hfileex" as (msr) "[%HSIEr Hfile]".
    assert (Hsst2 : neq_vec (and_vec (sstatus_read msr)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false)
      by (apply pop_sstatus_clear_neq; exact HSIEr).
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read msr)]> C).
    assert (Hpp10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.andi a5,2 *)
    iApply (wp_candi_s_scfg root_ppn γc Φ (mword_of_int (PP + 0x10)) (mword_of_int 15) (mword_of_int 2 : mword 6)
              P3 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              with "Hcfg Htlbinv Hpc Hfile Hi10 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
    set (P4 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (and_vec (P3 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6))))]> P3).
    assert (Ha5P3 : P3 !!! Regidx (mword_of_int 15 : mword 5) = sstatus_read msr)
      by (rewrite /P3; apply lookup_total_insert).
    assert (Hpp12 : add_vec_int (mword_of_int (PP + 0x10) : mword 64) 2 = mword_of_int (PP + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* +0x12 c.bnez a5 NOT taken (SIE = 0) *)
    assert (Ha5P4 : P4 !!! Regidx (mword_of_int 15 : mword 5)
                    = and_vec (sstatus_read msr) (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))).
    { rewrite /P4. rewrite lookup_total_insert. rewrite Ha5P3. reflexivity. }
    iApply (wp_cbnez_fall_s_scfg root_ppn γc Φ (mword_of_int (PP + 0x12)) (mword_of_int 15) (Cregidx (mword_of_int 7)) (mword_of_int 15)
              P4 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P4; exact Hsst2)
              with "Hcfg Htlbinv Hpc Hfile Hi12 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
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
    iApply (wp_vc_block_s root_ppn popoff_lw_prog Φ
              (VSt (PP + 0x14) po_lw_regs0 [] po_noff_cell0)
              (VSt (PP + 0x16) po_lw_regs1 [] po_noff_cell0)
              ρD P4 γc
              (dq:=DfracOwn 1)
 po_lw_run HmD
              with "Hcfg Htlbinv
                    Hpc Hfile Hbi14 [] [Hnoff]").
    { rewrite /vheap_own. cbn [vheap]. done. }
    { rewrite /vheap4_own. cbn [vheap4]. rewrite /po_noff_cell0.
      cbn [big_opL fst snd].
      rewrite HaD HvD. iFrame "Hnoff". }
    iIntros (M2) "%HmD1 Hcfg Htlbinv Hpc Hfile _ Hheap4".
    destruct HmD1 as [HmD1 HaD1].
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
    iApply (wp_bge_x0_fall_s_scfg root_ppn γc Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15)
              M2 (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5M2; exact Hnoffpos)
              with "Hcfg Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hcfg Htlbinv Hpc Hfile".
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
    iApply (wp_vc_block_s root_ppn popoff_decsw_prog Φ
              (VSt (PP + 0x1a) po_decsw_regs0 [] po_noff_cell0)
              (VSt (PP + 0x1e) po_decsw_regs1 [] po_noff_cell1)
              ρE M2 γc
              (dq:=DfracOwn 1)
 po_decsw_run HmE
              with "Hcfg Htlbinv
                    Hpc Hfile Hbi1a [] [Hnoffw]").
    { rewrite /vheap_own. cbn [vheap]. done. }
    { rewrite /vheap4_own. cbn [vheap4]. rewrite /po_noff_cell0.
      cbn [big_opL fst snd].
      rewrite HaE HvE. iFrame "Hnoffw". }
    iIntros (M3) "%HmE1 Hcfg Htlbinv Hpc Hfile _ Hheap4".
    destruct HmE1 as [HmE1 HaE1].
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
    (* ---- callee-saved x18/x19/x20/x21 (s2/s3/s4/s5): pop_off never writes
       them, so they are preserved from [m] through every straight-line block
       (via the block's [agree_off], since they are absent from the block's
       symbolic map) and through the mycpu() call (po_mycpu_out_s2..s5).  The
       strengthened postcondition needs these. *)
    assert (Hpres_M3 :
        M3 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)
      /\ M3 !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
    { repeat split.
      - rewrite (HaE1 (Regidx (mword_of_int 18 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 18 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s2.
        exact (HaA1 (Regidx (mword_of_int 18 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 19 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 19 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s3.
        exact (HaA1 (Regidx (mword_of_int 19 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 20 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 20 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s4.
        exact (HaA1 (Regidx (mword_of_int 20 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 21 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 21 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s5.
        exact (HaA1 (Regidx (mword_of_int 21 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 22 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 22 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s6.
        exact (HaA1 (Regidx (mword_of_int 22 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 23 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 23 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s7.
        exact (HaA1 (Regidx (mword_of_int 23 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 24 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 24 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s8.
        exact (HaA1 (Regidx (mword_of_int 24 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 25 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 25 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s9.
        exact (HaA1 (Regidx (mword_of_int 25 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 26 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 26 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s10.
        exact (HaA1 (Regidx (mword_of_int 26 : mword 5)) ltac:(vm_compute; reflexivity)).
      - rewrite (HaE1 (Regidx (mword_of_int 27 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite (HaD1 (Regidx (mword_of_int 27 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite Hmc_s11.
        exact (HaA1 (Regidx (mword_of_int 27 : mword 5)) ltac:(vm_compute; reflexivity)). }
    destruct Hpres_M3 as (H18M3 & H19M3 & H20M3 & H21M3 & H22M3 & H23M3 & H24M3 & H25M3 & H26M3 & H27M3).
    (* +0x1e c.bnez a5: both outcomes (noff-1 <> 0 / = 0) *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnz.
    - (* taken: skip the intena check, straight to the epilogue at +0x28 *)
      iApply (wp_cbnez_taken_s_zca_scfg root_ppn γc Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                M3 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5M3; exact Hnz)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
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
      iApply (wp_vc_block_s root_ppn mycpu_epilogue Φ
                (VSt (PP + 0x28) po_epi_regs0 mycpu_epi_heap [])
                (VSt (PP + 0x2e) po_epi_regs1 mycpu_epi_heap [])
                ρC M3 γc
                (dq:=DfracOwn 1)
 po_epilogue_run HmC
                with "Hcfg Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0] []").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        cbn [big_opL fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      { rewrite /vheap4_own. cbn [vheap4]. done. }
      iIntros (Mf) "%HmC1 Hcfg Htlbinv Hpc Hfile Hheap _".
      destruct HmC1 as [HmC1 HaC1].
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
      (* callee-saved x18..x21: this epilogue block runs from M3 directly, so
         [agree_off] gives Mf!!!k = M3!!!k, and [H*M3] closes to [m]. *)
      assert (H18F : Mf !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 18 : mword 5)) ltac:(vm_compute; reflexivity)). exact H18M3. }
      assert (H19F : Mf !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 19 : mword 5)) ltac:(vm_compute; reflexivity)). exact H19M3. }
      assert (H20F : Mf !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 20 : mword 5)) ltac:(vm_compute; reflexivity)). exact H20M3. }
      assert (H21F : Mf !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 21 : mword 5)) ltac:(vm_compute; reflexivity)). exact H21M3. }
      assert (H22F : Mf !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 22 : mword 5)) ltac:(vm_compute; reflexivity)). exact H22M3. }
      assert (H23F : Mf !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 23 : mword 5)) ltac:(vm_compute; reflexivity)). exact H23M3. }
      assert (H24F : Mf !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 24 : mword 5)) ltac:(vm_compute; reflexivity)). exact H24M3. }
      assert (H25F : Mf !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 25 : mword 5)) ltac:(vm_compute; reflexivity)). exact H25M3. }
      assert (H26F : Mf !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 26 : mword 5)) ltac:(vm_compute; reflexivity)). exact H26M3. }
      assert (H27F : Mf !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 27 : mword 5)) ltac:(vm_compute; reflexivity)). exact H27M3. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca_scfg root_ppn γc Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Mf
                (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
                ltac:(rewrite HraF; exact Hal0)
                with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HraF) in "Hpc".
      iEval (rewrite Hb1) in "Hp8". iEval (rewrite Hb2) in "Hp0".
      iDestruct (stack_own_2_intro with "Hp8 Hp0") as "Ht12".
      iEval (rewrite -Hspd2) in "Hstk".
      iDestruct (stack_own_split_2 (m !!! Regidx csp_rs1) 2 4 ltac:(lia) with "[$Ht12 $Hstk]") as "Htopf".
      iDestruct (stack_own_split_2 (m !!! Regidx csp_rs1) 4 n ltac:(lia) with "[$Htopf $Hdeep]") as "Hpstkf".
      iApply ("Hcont" $! Mf with "Hcfg Htlbinv Hpc Hfile [%] Hnoff Hint Hpstkf").
      { unfold callee_saved. repeat split; assumption. }
    - (* fall: noff-1 = 0, read intena (= 0), c.beqz taken to +0x28 *)
      iApply (wp_cbnez_fall_s_scfg root_ppn γc Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                M3 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5M3; exact Hnz)
                with "Hcfg Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      assert (Hpp20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.lw a5,124(a0): a5 := sext64 intenav (fractional cell: leaf) *)
      assert (HAint : add_vec (M3 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 124 : mword 12)) = a_int)
        by (rewrite Ha0M3; reflexivity).
      iApply (wp_clw_s_ram_scfg root_ppn γc Φ (mword_of_int (PP + 0x20)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 124) M3 intenav
                (dq:=DfracOwn 1) (dqm:=dqi)
 ltac:(vm_compute; discriminate)
                with "Hcfg Htlbinv Hpc Hfile Hi20 [Hint] [-]").
      { iEval (rewrite HAint). iExact "Hint". }
      iIntros "Hcfg Htlbinv Hpc Hfile Hint".
      iEval (rewrite HAint) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> M3).
      assert (Ha5P7 : P7 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 intenav)
        by (rewrite /P7; apply lookup_total_insert).
      assert (Hpp22 : add_vec_int (mword_of_int (PP + 0x20) : mword 64) 2 = mword_of_int (PP + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp22) in "Hpc".
      (* +0x22 c.beqz a5 TAKEN (intena = 0) *)
      iApply (wp_cbeqz_taken_s_zca_scfg root_ppn γc Φ (mword_of_int (PP + 0x22)) (mword_of_int 3) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P7 (dq:=DfracOwn 1)
 ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P7; exact Hint)
                ltac:(vm_compute; reflexivity)
                with "Hcfg Htlbinv Hpc Hfile Hi22 [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
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
      iApply (wp_vc_block_s root_ppn mycpu_epilogue Φ
                (VSt (PP + 0x28) po_epi_regs0 mycpu_epi_heap [])
                (VSt (PP + 0x2e) po_epi_regs1 mycpu_epi_heap [])
                ρC P7 γc
                (dq:=DfracOwn 1)
 po_epilogue_run HmC
                with "Hcfg Htlbinv
                      Hpc Hfile Hbi2 [Hp8 Hp0] []").
      { rewrite /vheap_own. cbn [vheap]. rewrite /mycpu_epi_heap.
        cbn [big_opL fst snd]. rewrite HaraC Has0C Hv33C Hv34C.
        iFrame "Hp8 Hp0". }
      { rewrite /vheap4_own. cbn [vheap4]. done. }
      iIntros (Mf) "%HmC1 Hcfg Htlbinv Hpc Hfile Hheap _".
      destruct HmC1 as [HmC1 HaC1].
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
      (* callee-saved x18..x21: this epilogue block runs from P7 = <[x15]>M3, so
         [agree_off] gives Mf!!!k = P7!!!k, one insert peels x15, then [H*M3]. *)
      assert (H18F : Mf !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 18 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H18M3. }
      assert (H19F : Mf !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 19 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H19M3. }
      assert (H20F : Mf !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 20 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H20M3. }
      assert (H21F : Mf !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 21 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H21M3. }
      assert (H22F : Mf !!! Regidx (mword_of_int 22 : mword 5) = m !!! Regidx (mword_of_int 22 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 22 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H22M3. }
      assert (H23F : Mf !!! Regidx (mword_of_int 23 : mword 5) = m !!! Regidx (mword_of_int 23 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 23 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H23M3. }
      assert (H24F : Mf !!! Regidx (mword_of_int 24 : mword 5) = m !!! Regidx (mword_of_int 24 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 24 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H24M3. }
      assert (H25F : Mf !!! Regidx (mword_of_int 25 : mword 5) = m !!! Regidx (mword_of_int 25 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 25 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H25M3. }
      assert (H26F : Mf !!! Regidx (mword_of_int 26 : mword 5) = m !!! Regidx (mword_of_int 26 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 26 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H26M3. }
      assert (H27F : Mf !!! Regidx (mword_of_int 27 : mword 5) = m !!! Regidx (mword_of_int 27 : mword 5)).
      { rewrite (HaC1 (Regidx (mword_of_int 27 : mword 5)) ltac:(vm_compute; reflexivity)).
        rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact H27M3. }
      (* +0x2e c.ret *)
      iApply (wp_cret_s_zca_scfg root_ppn γc Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Mf
                (dq:=DfracOwn 1)
 ltac:(vm_compute; discriminate)
                ltac:(rewrite HraF; exact Hal0)
                with "Hcfg Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hcfg Htlbinv Hpc Hfile".
      iEval (rewrite HraF) in "Hpc".
      iEval (rewrite Hb1) in "Hp8". iEval (rewrite Hb2) in "Hp0".
      iDestruct (stack_own_2_intro with "Hp8 Hp0") as "Ht12".
      iEval (rewrite -Hspd2) in "Hstk".
      iDestruct (stack_own_split_2 (m !!! Regidx csp_rs1) 2 4 ltac:(lia) with "[$Ht12 $Hstk]") as "Htopf".
      iDestruct (stack_own_split_2 (m !!! Regidx csp_rs1) 4 n ltac:(lia) with "[$Htopf $Hdeep]") as "Hpstkf".
      iApply ("Hcont" $! Mf with "Hcfg Htlbinv Hpc Hfile [%] Hnoff Hint Hpstkf").
      { unfold callee_saved. repeat split; assumption. }
  Qed.



End WpPopOffTopSec.

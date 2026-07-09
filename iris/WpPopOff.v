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

   New leaves: [wp_cbeqz_fall_s] (c.beqz fall-through), [wp_bge_x0_fall_s]
   (32-bit blez not-taken), [wp_fence_s] (fence rw,w -- release() needs it;
   defined here with the rest of the new leaf kit), [wp_csrr_sstatus_s]
   (read-only csrr of sstatus). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import WpGprCsrwCommon.
(* QUALIFIED (no Import): sstatus SIE-bit bridges for the pop_off interrupt-off fact. *)
Require WpGprCsrwC.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvExtras RiscvTryStep RiscvFetchExec.
Require Import MinstretInv InstrBytes.
Require Import WpAdd WpFetch WpLoad WpDecode WpLeafCommon WpEntry WpEntryNew WpAuipc.
Require Import WpGpr WpGprAddi WpGprRvc WpGprShift WpGprJalr WpGprStore WpGprLogic WpGprAuipc WpGprLoad.
Require Import SmodeCore WpSmodeGpr WpMemsetS WpSpinNew WpKernelvecNew WpPushOff.
Require Import WpPushOffMem WpPushOffCsr WpMycpu WpPushOffTop WpMemsetInstr WpHolding.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
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
Lemma ppdec_jal_mycpu s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x495000ef : mword 32)) s
  = Some (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. pp_dbase s Hpriv. Qed.

(* +0x0c  0x100027f3  csrr a5,sstatus  (csrrs a5,sstatus,x0) *)
Lemma ppdec_csrr s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x100027f3 : mword 32)) s
  = Some (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS), s).
Proof. intro Hpriv. pp_dbase s Hpriv. Qed.

(* +0x16  0x02f05363  blez a5,+0x26  (bge x0,a5) *)
Lemma ppdec_blez s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x02f05363 : mword 32)) s
  = Some (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. intro Hpriv. pp_dbase s Hpriv. Qed.

(* release +0x16  0x0310000f  fence rw,w *)
Lemma ppdec_fence s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x0310000f : mword 32)) s
  = Some (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                 Regidx (mword_of_int 0), Regidx (mword_of_int 0)), s).
Proof. intro Hpriv. pp_dbase s Hpriv. Qed.

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

Lemma exec_sail_barrier (b : Arch.barrier) s :
  exec (sail_barrier b) s = Some (tt, s).
Proof. reflexivity. Qed.

Lemma exec_is_fiom_active_S (menvcfg0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  exec (is_fiom_active tt) s
    = Some (eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1"), s).
Proof.
  intros Hcp Hmenv. unfold is_fiom_active.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg cur_privilege s)).
  rewrite Hcp. cbn match.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_read_reg menvcfg s)).
  rewrite Hmenv. apply exec_returnM.
Qed.

Lemma exec_execute_FENCE_rw_w (menvcfg0 : mword 64) s :
  register_lookup cur_privilege s.(sregs) = Supervisor ->
  register_lookup menvcfg s.(sregs) = menvcfg0 ->
  eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
  exec (execute (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                        Regidx (mword_of_int 0), Regidx (mword_of_int 0)))) s
    = Some (RETIRE_SUCCESS, s).
Proof.
  intros Hcp Hmenv Hfiom.
  change (execute (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                          Regidx (mword_of_int 0), Regidx (mword_of_int 0))))
    with (execute_FENCE (mword_of_int 0) (mword_of_int 3) (mword_of_int 1)
            (Regidx (mword_of_int 0)) (Regidx (mword_of_int 0))).
  unfold execute_FENCE.
  rewrite (exec_bind_Some _ _ _ _ _ (exec_is_fiom_active_S menvcfg0 s Hcp Hmenv)).
  rewrite Hfiom.
  unfold effective_fence_set.
  cbn match beta zeta.
  match goal with |- context[if ?g then _ else _] =>
    replace g with true by (vm_compute; reflexivity)
  end.
  cbn match.
  rewrite (exec_bind0_Some _ _ _ _ _ (exec_sail_barrier _ s)).
  apply exec_returnM.
Qed.

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
  Lemma wp_cbeqz_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm8 : mword 8) (rs : cregidx) (rd1 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = false ->
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
      pc_is (add_vec_int pc 2) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hrs Hrd1 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hma with "Hfmap") as "[Hrac Hfba]".
    iDestruct (gpr_pt_value rd1 (m !!! Regidx rd1) s_pc with "Hreg Hrac") as %Lva.
    iDestruct ("Hfba" with "Hrac") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc. rewrite Hrs.
      change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
      apply exec_execute_BTYPE_BEQ_fall. unfold rvv.
      rewrite Lva.
      replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 2)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- 32-bit bge x0,rs2 (blez rs2) FALL-THROUGH: rs2 signed-positive ---- *)
  Lemma wp_bge_x0_fall_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (imm : mword 13) (rs2 : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    uint rs2 <> 0 ->
    zopz0zKzJ_s zero_reg (m !!! Regidx rs2) = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hrs2 Hcmp)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false (BTYPE (imm, Regidx rs2, Regidx (mword_of_int 0), BGE))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    assert (Hmb : m !! Regidx rs2 = Some (m !!! Regidx rs2))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    iDestruct (big_sepM_lookup_acc _ _ _ _ Hmb with "Hfmap") as "[Hrbc Hfbb]".
    iDestruct (gpr_pt_value rs2 (m !!! Regidx rs2) s_pc with "Hreg Hrbc") as %Lvb.
    iDestruct ("Hfbb" with "Hrbc") as "Hfmap".
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply exec_execute_BTYPE_BGE_fall. unfold rvv. rewrite Lvb.
      replace (Z.eqb (uint (mword_of_int 0 : mword 5)) 0) with true
        by (vm_compute; reflexivity).
      cbn match. exact Hcmp. }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR; [iPureIntro; exact Hdom | iExact "Hfmap"].
  Qed.

  (* ---- fence rw,w: a pure no-op step (Supervisor, FIOM = 0) ---- *)
  Lemma wp_fence_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    eq_vec (_get_MEnvcfg_FIOM menvcfg0) ('b"1") = false ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                           Regidx (mword_of_int 0), Regidx (mword_of_int 0))) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE HFIOM)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] Hfile Hinstr Hcont".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false
              (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 1 : mword 4,
                      Regidx (mword_of_int 0), Regidx (mword_of_int 0)))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hmenv") as %Lmenv.
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_pc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lmenv_pc : register_lookup menvcfg s_pc.(sregs) = menvcfg0)
      by (unfold s_pc; tmig; exact Lmenv).
    iModIntro. iExists s_pc.
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_FENCE_rw_w menvcfg0 s_pc Lpriv_pc Lmenv_pc HFIOM). }
    iSplitL "Hreg Hmem". { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC s_pc.(sregs) = add_vec_int pc 4)
      by (unfold s_pc; rewrite register_lookup_set; reflexivity).
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] Hfile").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
  Qed.

  (* ---- csrr rd,sstatus (read-only CSRRS with rs1 = x0) ---- *)
  Lemma wp_csrr_sstatus_s (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 4) -∗
      gpr_file (<[Regidx rd := regval_into_reg (sstatus_read mstatus0)]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hrd)
      "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
       [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC & %HmisaU & %HmisaM &
        %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc false
              (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx rd, CSRRS))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hpriv") as %Lpriv.
    iDestruct (reg_valid_dq with "Hreg Hms") as %Lms.
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hmd : m !! Regidx rd = Some (m !!! Regidx rd))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 4) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 4)).
    assert (Lpriv_spc : register_lookup cur_privilege s_pc.(sregs) = Supervisor)
      by (unfold s_pc; tmig; exact Lpriv).
    assert (Lms_spc : register_lookup mstatus s_pc.(sregs) = mstatus0)
      by (unfold s_pc; tmig; exact Lms).
    assert (Lmisa_spc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
    iDestruct (big_sepM_insert_acc _ _ _ _ Hmd with "Hfmap") as "[Hrdc Hfins]".
    rewrite (gpr_pt_nz rd _ Hrd).
    iMod (reg_update _ (R_bitvector_64 (gpr_of_Z (uint rd))) _
            (regval_into_reg (sstatus_read mstatus0)) with "Hreg Hrdc") as "[Hreg Hrdc]".
    iDestruct ("Hfins" $! (regval_into_reg (sstatus_read mstatus0)) with "[Hrdc]") as "Hfmap".
    { rewrite (gpr_pt_nz rd _ Hrd). iExact "Hrdc". }
    iModIntro.
    iExists (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
               (regval_into_reg (sstatus_read mstatus0))).
    iSplitR.
    { iPureIntro. rewrite Hpceq. fold s_pc.
      apply (exec_execute_csrr_sstatus rd mstatus0 s_pc
               Lpriv_spc Lms_spc
               ltac:(rewrite Lmisa_spc; exact HmisaS) Hrd). }
    iSplitL "Hreg Hmem".
    { unfold s_pc, set_reg; cbn [sregs mem]. iFrame "Hreg Hmem". }
    iIntros "Hhs' Hpc'".
    assert (Lnpc : register_lookup nextPC
             (set_reg s_pc (R_bitvector_64 (gpr_of_Z (uint rd)))
                (regval_into_reg (sstatus_read mstatus0))).(sregs)
             = add_vec_int pc 4).
    { unfold s_pc; cbn [sregs]. tmig. rewrite register_lookup_set. reflexivity. }
    iEval (rewrite Lnpc) in "Hpc'".
    iApply ("Hcont" with "Hhs' Hpriv Hms Hmie Hmdl Hmenv [Hsatp Htlb Hpbytes Hpmp]
                          [$Hpc' $Hnpc] [Hfmap]").
    { iApply (tlb_inv_close root_ppn satp0 tlbvec_f Hmode Hasid Hppn Hconsf with "Hsatp Htlb Hpbytes Hpmp"). }
    iSplitR.
    { iPureIntro. intro r. rewrite dom_insert_L. apply elem_of_union_r. apply Hdom. }
    iExact "Hfmap".
  Qed.

End WpPopOffLeaves.

(* ===================================================================== *)
(* [instr] facts for pop_off's instructions from [kernel_text].           *)
(* ===================================================================== *)
Section WpPopOffInstr.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Notation PP := KernelSyms.pop_off.

  Lemma ppi_00 : kernel_text -∗ instr (mword_of_int (PP + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (PP + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (PP + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma ppi_02 : kernel_text -∗ instr (mword_of_int (PP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc4 (PP + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int 0xe022e406 : mword 32)
    (mword_of_int (PP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma ppi_04 : kernel_text -∗ instr (mword_of_int (PP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc2 (PP + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma ppi_06 : kernel_text -∗ instr (mword_of_int (PP + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (PP + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int 0x00ef0800 : mword 32)
    (mword_of_int (PP + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma ppi_08 : kernel_text -∗ instr (mword_of_int (PP + 0x08) : mword 64) false (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PP + 0x08)%Z (mword_of_int 0x495000ef : mword 32)
    (mword_of_int (PP + 0x08) : mword 64) (JAL (mword_of_int 0xc94 : mword 21, Regidx (mword_of_int 1))) ppdec_jal_mycpu. Qed.

  Lemma ppi_0c : kernel_text -∗ instr (mword_of_int (PP + 0x0c) : mword 64) false (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)).
  Proof. mk_base (PP + 0x0c)%Z (mword_of_int 0x100027f3 : mword 32)
    (mword_of_int (PP + 0x0c) : mword 64) (CSRReg (csr_sstatus, Regidx (mword_of_int 0), Regidx (mword_of_int 15), CSRRS)) ppdec_csrr. Qed.

  Lemma ppi_10 : kernel_text -∗ instr (mword_of_int (PP + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_rvc2 (PP + 0x10)%Z (mword_of_int 0x8b89 : mword 16)
    (mword_of_int (PP + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) ppdec_andi ppexec_andi2. Qed.

  Lemma ppi_12 : kernel_text -∗ instr (mword_of_int (PP + 0x12) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc4 (PP + 0x12)%Z (mword_of_int 0xef99 : mword 16) (mword_of_int 0x5d3cef99 : mword 32)
    (mword_of_int (PP + 0x12) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 15 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ppdec_bnez1e hexec_bnez. Qed.

  Lemma ppi_14 : kernel_text -∗ instr (mword_of_int (PP + 0x14) : mword 64) true (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc2 (PP + 0x14)%Z (mword_of_int 0x5d3c : mword 16)
    (mword_of_int (PP + 0x14) : mword 64) (LOAD (mword_of_int 120, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) podec_lw poexec_lw. Qed.

  Lemma ppi_16 : kernel_text -∗ instr (mword_of_int (PP + 0x16) : mword 64) false (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PP + 0x16)%Z (mword_of_int 0x02f05363 : mword 32)
    (mword_of_int (PP + 0x16) : mword 64) (BTYPE (mword_of_int 0x26 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) ppdec_blez. Qed.

  Lemma ppi_1a : kernel_text -∗ instr (mword_of_int (PP + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc4 (PP + 0x1a)%Z (mword_of_int 0x37fd : mword 16) (mword_of_int 0xdd3c37fd : mword 32)
    (mword_of_int (PP + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) ppdec_addiwm1 exec_execute_C_ADDIW. Qed.

  Lemma ppi_1c : kernel_text -∗ instr (mword_of_int (PP + 0x1c) : mword 64) true (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc2 (PP + 0x1c)%Z (mword_of_int 0xdd3c : mword 16)
    (mword_of_int (PP + 0x1c) : mword 64) (STORE (mword_of_int 120, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 4)) podec_sw120 poexec_sw120. Qed.

  Lemma ppi_1e : kernel_text -∗ instr (mword_of_int (PP + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc4 (PP + 0x1e)%Z (mword_of_int 0xe789 : mword 16) (mword_of_int 0x5d7ce789 : mword 32)
    (mword_of_int (PP + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ppdec_bnez0a hexec_bnez. Qed.

  Lemma ppi_20 : kernel_text -∗ instr (mword_of_int (PP + 0x20) : mword 64) true (LOAD (mword_of_int 124, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc2 (PP + 0x20)%Z (mword_of_int 0x5d7c : mword 16)
    (mword_of_int (PP + 0x20) : mword 64) (LOAD (mword_of_int 124, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) ppdec_lw124 ppexec_lw124. Qed.

  Lemma ppi_22 : kernel_text -∗ instr (mword_of_int (PP + 0x22) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc4 (PP + 0x22)%Z (mword_of_int 0xc399 : mword 16) (mword_of_int 0x6073c399 : mword 32)
    (mword_of_int (PP + 0x22) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) ppdec_beqz06 exec_execute_C_BEQZ. Qed.

  Lemma ppi_28 : kernel_text -∗ instr (mword_of_int (PP + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc2 (PP + 0x28)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PP + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma ppi_2a : kernel_text -∗ instr (mword_of_int (PP + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc4 (PP + 0x2a)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int 0x01416402 : mword 32)
    (mword_of_int (PP + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma ppi_2c : kernel_text -∗ instr (mword_of_int (PP + 0x2c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc2 (PP + 0x2c)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PP + 0x2c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma ppi_2e : kernel_text -∗ instr (mword_of_int (PP + 0x2e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (PP + 0x2e)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x65178082 : mword 32)
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

  Lemma wp_cbnez_taken_s_zca (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
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
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    neq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗ instr pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is tgt -∗ gpr_file m -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE Hrs Hrd1 Hcmp Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BNE))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
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
      assert (Htk : neq_vec (rvv rd1 s_pc) (rvv (zero_extend' 5 ('b"00") : mword 5) s_pc) = true).
      { unfold rvv. rewrite Lva.
        replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
          by (vm_compute; reflexivity).
        cbn match. exact Hcmp. }
      epose proof (exec_execute_BTYPE_BNE_taken_zca (sign_extend' 13 (concat_vec imm8 ('b"0")))
                     (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. fold tgt in Hred.
      exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc ltac:(rewrite Lmisa_pc; exact HmisaC))). }
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

  Lemma wp_cbeqz_taken_s_zca (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
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
    creg2reg_idx rs = Regidx rd1 ->
    uint rd1 <> 0 ->
    eq_vec (m !!! Regidx rd1) zero_reg = true ->
    eq_vec (access_vec_dec tgt 0) ('b"0") = true ->
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
    intros tgt HN HSIE HMPRV HSXL Hmm HPBMTE Hrs Hrd1 Hcmp Hal0.
    iIntros "#Hhw #Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv
             [Hpc Hnpc] [%Hdom Hfmap] Hinstr Hcont".
    iPoseProof "Hhw" as "#Hhwc".
    iDestruct "Hhwc" as (misa0 mseccfg0 pmar0 elp0)
      "(#Hmisa & #Hmseccfg & #Hpma & #Hhtif & #Help & %HmisaS & %HmisaC &
        %HmisaU & %HmisaM & %Hpma_all & %Hseccfg1 & %Hseccfg2 & %Help_np & %HmisaA)".
    iApply (wp_instr_s_config_tlbinv root_ppn E Φ pc true (BTYPE (sign_extend' 13 (concat_vec imm8 ('b"0")), zreg, creg2reg_idx rs, BEQ))
              mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hinstr").
    iIntros (σ Hpceq satp0 tlbvec_f Hmode Hasid Hppn Hconsf)
      "Hpriv Hsatp Hms Hmie Hmdl Hmenv Hpmp Htlb Hpbytes Hsi".
    iDestruct "Hsi" as "[Hreg Hmem]".
    iDestruct (reg_valid_dq with "Hreg Hmisa") as %Lmisa.
    assert (Hma : m !! Regidx rd1 = Some (m !!! Regidx rd1))
      by (apply lookup_lookup_total_dom; apply Hdom).
    iMod (reg_update _ nextPC _ (add_vec_int pc 2) with "Hreg Hnpc") as "[Hreg Hnpc]".
    set (s_pc := set_reg σ nextPC (add_vec_int pc 2)).
    assert (Hpcv : register_lookup PC s_pc.(sregs) = pc).
    { unfold s_pc, set_reg; cbn [sregs].
      rewrite irrelevant_register_set; [ exact Hpceq | vm_compute; reflexivity ]. }
    assert (Lmisa_pc : register_lookup misa s_pc.(sregs) = misa0)
      by (unfold s_pc; tmig; exact Lmisa).
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
      epose proof (exec_execute_BTYPE_BEQ_taken_zca (sign_extend' 13 (concat_vec imm8 ('b"0")))
                     (zero_extend' 5 ('b"00")) rd1 s_pc Htk) as Hred.
      rewrite Hpcv in Hred. fold tgt in Hred.
      exact (Hred Hal0 (exec_currentlyEnabled_Zca s_pc ltac:(rewrite Lmisa_pc; exact HmisaC))). }
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

End WpPopOffTakenZca.


(* ===================================================================== *)
(* wp_pop_off -- S-mode whole-function WP for pop_off().                  *)
(* Preconditions (beyond the standard S-mode config): interrupts are OFF  *)
(* (mstatus.SIE = 0, via the [Hsst2] premise on the sstatus view), the    *)
(* per-cpu noff is signed-POSITIVE, and the saved intena is 0 (so the     *)
(* csrsi that would re-enable interrupts is provably skipped).            *)
(* ===================================================================== *)
(* SIE=0 (folded into smode_config) gives pop_off's interrupt-off fact
   [sstatus & 2 = 0] with mstatus0 hidden.  Mirrors WpRelease's bridge. *)
Lemma pop_mword1_zero_of_ne_one (x : mword 1) :
  eq_vec x ('b"1") = false -> x = ('b"0" : mword 1).
Proof.
  intro H. apply eq_vec_false_iff in H. apply bv_eq.
  pose proof (bv_unsigned_in_range _ x) as Hr.
  assert (Hmod : bv_modulus 1 = 2) by (vm_compute; reflexivity).
  rewrite Hmod in Hr.
  assert (H1 : bv_unsigned ('b"1" : mword 1) = 1) by (vm_compute; reflexivity).
  assert (H0 : bv_unsigned ('b"0" : mword 1) = 0) by (vm_compute; reflexivity).
  rewrite H0.
  assert (Hne : bv_unsigned x <> 1).
  { intro Hc. apply H. apply bv_eq. rewrite H1. exact Hc. }
  lia.
Qed.

Lemma pop_sstatus_clear_neq (m : mword 64) :
  eq_vec (_get_Mstatus_SIE m) ('b"1") = false ->
  neq_vec (and_vec (sstatus_read m)
             (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false.
Proof.
  intro HSIE.
  unfold neq_vec. apply negb_false_iff. apply eq_vec_true_iff.
  assert (Hz : _get_Mstatus_SIE m = ('b"0" : mword 1))
    by (apply pop_mword1_zero_of_ne_one; exact HSIE).
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

Section WpPopOffTopSec.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Notation PP := KernelSyms.pop_off.

  Lemma wp_pop_off (root_ppn : mword 44) (γc : gname) E (Φ : mval -> iProp Σ)
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
    (* noff >= 1 (signed) *)
    zopz0zKzJ_s zero_reg (sign_extend' 64 noffv) = false ->
    (* saved intena is 0 *)
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
          mf !!! Regidx (mword_of_int 10 : mword 5) = a0v /\
          mf !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5) /\
          mf !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5) /\
          mf !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5) /\
          mf !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5) ⌝) -∗
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
    (* unbundle the ambient config; the interrupt-off sstatus fact follows from SIE=0 *)
    iDestruct (smode_config_unbundle γc (DfracOwn 1) with "Hcfg")
      as "(Hhw & Hinv & Hhs & Hpriv & Hmsb & Hmieb & Hmenvb)".
    iDestruct "Hhw" as "#Hhw". iDestruct "Hinv" as "#Hinv".
    iDestruct "Hmsb" as (mstatus0) "(Hms & Hgc & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmieb" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenvb" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %Hlpe & %Hfiom)".
    assert (Hsst2 : neq_vec (and_vec (sstatus_read mstatus0)
              (sign_extend' 64 (sign_extend' 12 (mword_of_int 2 : mword 6)))) zero_reg = false)
      by (apply pop_sstatus_clear_neq; exact HSIE).
    iPoseProof (ppi_00 with "Htext") as "Hi00".
    iPoseProof (ppi_02 with "Htext") as "Hi02".
    iPoseProof (ppi_04 with "Htext") as "Hi04".
    iPoseProof (ppi_06 with "Htext") as "Hi06".
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
    iPoseProof (ppi_28 with "Htext") as "Hi28".
    iPoseProof (ppi_2a with "Htext") as "Hi2a".
    iPoseProof (ppi_2c with "Htext") as "Hi2c".
    iPoseProof (ppi_2e with "Htext") as "Hi2e".
    (* +0x00 c.addi sp,-16 *)
    iApply (wp_caddi_gpr_s_config root_ppn E Φ pcE csp_rs1 (mword_of_int 48 : mword 6) m
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi00 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P1 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))]> m).
    assert (HspP1 : P1 !!! Regidx csp_rs1 = spd)
      by (rewrite /P1; apply lookup_total_insert).
    assert (Hpp02 : add_vec_int pcE 2 = mword_of_int (PP + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* +0x02 c.sdsp ra,8(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x02)) (mword_of_int 1 : mword 6) (mword_of_int 1 : mword 5)
              P1 vp8 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi02 [Hp8] [-]").
    { iEval (rewrite HspP1). iExact "Hp8". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp8".
    assert (HraP1 : P1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5))
      by (rewrite /P1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HspP1 HraP1) in "Hp8".
    assert (Hpp04 : add_vec_int (mword_of_int (PP + 0x02) : mword 64) 2 = mword_of_int (PP + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* +0x04 c.sdsp s0,0(sp) *)
    iApply (wp_csdsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x04)) (mword_of_int 0 : mword 6) (mword_of_int 8 : mword 5)
              P1 vp0 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi04 [Hp0] [-]").
    { iEval (rewrite HspP1). iExact "Hp0". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp0".
    assert (Hs0P1 : P1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5))
      by (rewrite /P1; rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite HspP1 Hs0P1) in "Hp0".
    assert (Hpp06 : add_vec_int (mword_of_int (PP + 0x04) : mword 64) 2 = mword_of_int (PP + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* +0x06 c.addi4spn s0,sp,16 *)
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Φ (mword_of_int (PP + 0x06)) (Cregidx (mword_of_int 0)) (mword_of_int 4 : mword 8) (mword_of_int 8 : mword 5)
              P1 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE 
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi06 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (add_vec (P1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm (mword_of_int 4 : mword 8))))]> P1).
    assert (Hpp08 : add_vec_int (mword_of_int (PP + 0x06) : mword 64) 2 = mword_of_int (PP + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* +0x08 jal ra,mycpu; the whole mycpu() *)
    assert (HspP2 : P2 !!! Regidx csp_rs1 = spd).
    { rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate]. exact HspP1. }
    assert (HspP2r : (<[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int (mword_of_int (PP + 0x08) : mword 64) 4)]> P2) !!! Regidx csp_rs1 = spd)
      by (rewrite lookup_total_insert_ne; [ exact HspP2 | vm_compute; discriminate ]).
    iApply (wp_pushoff_call_mycpu root_ppn γc E Φ (mword_of_int (PP + 0x08)) (mword_of_int 0xc94 : mword 21) P2 vfra vfs0
              mstatus0 mie_v mdv0 menvcfg0
              HN ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hlpe Hfiom Hleg
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
    set (C := po_mycpu_out (mword_of_int (PP + 0x08)) P2).
    (* +0x0c csrr a5,sstatus *)
    iApply (wp_csrr_sstatus_s root_ppn E Φ (mword_of_int (PP + 0x0c)) (mword_of_int 15) C
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi0c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P3 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sstatus_read mstatus0)]> C).
    assert (Hpp10 : add_vec_int (mword_of_int (PP + 0x0c) : mword 64) 4 = mword_of_int (PP + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* +0x10 c.andi a5,2 *)
    iApply (wp_candi_s root_ppn E Φ (mword_of_int (PP + 0x10)) (mword_of_int 15) (mword_of_int 2 : mword 6)
              P3 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
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
    (* +0x14 c.lw a5,120(a0): a5 := sext64 noffv *)
    assert (Ha0C : C !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /C po_mycpu_out_a0.
      rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    assert (Ha0P4 : P4 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Ha0C. }
    assert (HAnoff4 : add_vec (P4 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 120 : mword 12)) = a_noff)
      by (rewrite Ha0P4; reflexivity).
    iApply (wp_clw_s_ram root_ppn E Φ (mword_of_int (PP + 0x14)) (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 120) P4 noffv mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi14 [Hnoff] [-]").
    { iEval (rewrite HAnoff4). iExact "Hnoff". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite HAnoff4) in "Hnoff".
    set (P5 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 noffv)]> P4).
    assert (Hpp16 : add_vec_int (mword_of_int (PP + 0x14) : mword 64) 2 = mword_of_int (PP + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    (* +0x16 blez a5 NOT taken (noff >= 1) *)
    assert (Ha5P5 : P5 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 noffv)
      by (rewrite /P5; apply lookup_total_insert).
    iApply (wp_bge_x0_fall_s root_ppn E Φ (mword_of_int (PP + 0x16)) (mword_of_int 0x26 : mword 13) (mword_of_int 15)
              P5 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE 
              ltac:(vm_compute; discriminate)
              ltac:(rewrite Ha5P5; exact Hnoffpos)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi16 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    assert (Hpp1a : add_vec_int (mword_of_int (PP + 0x16) : mword 64) 4 = mword_of_int (PP + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    (* +0x1a c.addiw a5,-1 *)
    iApply (wp_caddiw_s root_ppn E Φ (mword_of_int (PP + 0x1a)) (mword_of_int 15) (mword_of_int 63 : mword 6)
              P5 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1a [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
    set (P6 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg
        (sign_extend' 64 (subrange_vec_dec
           (add_vec (P5 !!! Regidx (mword_of_int 15 : mword 5)) (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))]> P5).
    assert (Ha5P6 : P6 !!! Regidx (mword_of_int 15 : mword 5) = nv1).
    { rewrite /P6. rewrite lookup_total_insert. rewrite Ha5P5. reflexivity. }
    assert (Hpp1c : add_vec_int (mword_of_int (PP + 0x1a) : mword 64) 2 = mword_of_int (PP + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* +0x1c c.sw a5,120(a0): noff := noff-1 *)
    assert (Ha0P6 : P6 !!! Regidx (mword_of_int 10 : mword 5) = a0v).
    { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
      exact Ha0P4. }
    assert (HAnoff6 : add_vec (P6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 120 : mword 12)) = a_noff)
      by (rewrite Ha0P6; reflexivity).
    iApply (wp_csw_s_ram root_ppn E Φ (mword_of_int (PP + 0x1c)) (mword_of_int 15) (mword_of_int 10)
              (mword_of_int 120) P6 noffv mstatus0 mie_v mdv0 menvcfg0
              (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1c [Hnoff] [-]").
    { iEval (rewrite HAnoff6). iExact "Hnoff". }
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hnoff".
    iEval (rewrite HAnoff6 Ha5P6) in "Hnoff".
    assert (Hpp1e : add_vec_int (mword_of_int (PP + 0x1c) : mword 64) 2 = mword_of_int (PP + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    (* +0x1e c.bnez a5: both outcomes (noff-1 <> 0 / = 0) *)
    destruct (neq_vec nv1 zero_reg) eqn:Hnz.
    - (* taken: skip the intena check, straight to the epilogue at +0x28 *)
      iApply (wp_cbnez_taken_s_zca root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P6 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnz)
                ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpc28 : add_vec (mword_of_int (PP + 0x1e) : mword 64)
                        (sign_extend' 64 (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0"))))
                      = mword_of_int (PP + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc28) in "Hpc".
      (* ---- epilogue from P6 ---- *)
      assert (HspC : C !!! Regidx csp_rs1 = spd).
      { rewrite /C po_mycpu_out_csp. exact HspP2. }
      assert (HspP6 : P6 !!! Regidx csp_rs1 = spd).
      { rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x28)) (mword_of_int 1) (mword_of_int 1 : mword 5)
                P6 (m !!! Regidx (mword_of_int 1 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi28 [Hp8]").
      { iEval (rewrite HspP6). iExact "Hp8". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp8".
      iEval (rewrite HspP6) in "Hp8".
      set (Q1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> P6).
      assert (HspQ1 : Q1 !!! Regidx csp_rs1 = spd)
        by (rewrite /Q1; rewrite lookup_total_insert_ne; [ exact HspP6 | vm_compute; discriminate ]).
      assert (Hpp2a : add_vec_int (mword_of_int (PP + 0x28) : mword 64) 2 = mword_of_int (PP + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x2a)) (mword_of_int 0) (mword_of_int 8 : mword 5)
                Q1 (m !!! Regidx (mword_of_int 8 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2a [Hp0]").
      { iEval (rewrite HspQ1). iExact "Hp0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp0".
      iEval (rewrite HspQ1) in "Hp0".
      set (Q2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q1).
      assert (Hpp2c : add_vec_int (mword_of_int (PP + 0x2a) : mword 64) 2 = mword_of_int (PP + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (PP + 0x2c)) csp_rs1 (mword_of_int 16 : mword 6) Q2
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2c [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      set (Q3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> Q2).
      assert (Hpp2e : add_vec_int (mword_of_int (PP + 0x2c) : mword 64) 2 = mword_of_int (PP + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      assert (HraQ3 : Q3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. apply lookup_total_insert. }
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Q3
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraQ3; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      iEval (rewrite HraQ3) in "Hpc".
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom
                   with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
      iApply ("Hcont" with "Hcfg Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Q3. iFrame "Hfile". iPureIntro.
        split; [exact HraQ3|]. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. apply lookup_total_insert.
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s1.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Q3. rewrite lookup_total_insert.
          assert (HspQ2 : Q2 !!! Regidx csp_rs1 = spd)
            by (rewrite /Q2; rewrite lookup_total_insert_ne; [ exact HspQ1 | vm_compute; discriminate ]).
          rewrite HspQ2.
          rewrite /spd po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_tp.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          exact Ha0P6.
        - (* s2 (x18) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s2.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s3 (x19) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s3.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s4 (x20) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s4.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s5 (x21) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s5.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
      }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
    - (* fall: noff-1 = 0, read intena (= 0), c.beqz taken to +0x28 *)
      iApply (wp_cbnez_fall_s root_ppn E Φ (mword_of_int (PP + 0x1e)) (mword_of_int 5) (Cregidx (mword_of_int 7)) (mword_of_int 15)
                P6 mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE 
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
                ltac:(rewrite Ha5P6; exact Hnz)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi1e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      assert (Hpp20 : add_vec_int (mword_of_int (PP + 0x1e) : mword 64) 2 = mword_of_int (PP + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp20) in "Hpc".
      (* +0x20 c.lw a5,124(a0): a5 := sext64 intenav *)
      assert (HAint6 : add_vec (P6 !!! Regidx (mword_of_int 10 : mword 5)) (sign_extend' 64 (mword_of_int 124 : mword 12)) = a_int)
        by (rewrite Ha0P6; reflexivity).
      iApply (wp_clw_s_ram root_ppn E Φ (mword_of_int (PP + 0x20)) (mword_of_int 15) (mword_of_int 10)
                (mword_of_int 124) P6 intenav mstatus0 mie_v mdv0 menvcfg0
                (dq:=DfracOwn 1) (dqm:=dqi)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi20 [Hint] [-]").
      { iEval (rewrite HAint6). iExact "Hint". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hint".
      iEval (rewrite HAint6) in "Hint".
      set (P7 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 intenav)]> P6).
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
      (* ---- epilogue from P7 ---- *)
      assert (HspC : C !!! Regidx csp_rs1 = spd).
      { rewrite /C po_mycpu_out_csp. exact HspP2. }
      assert (HspP7 : P7 !!! Regidx csp_rs1 = spd).
      { rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        exact HspC. }
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x28)) (mword_of_int 1) (mword_of_int 1 : mword 5)
                P7 (m !!! Regidx (mword_of_int 1 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi28 [Hp8]").
      { iEval (rewrite HspP7). iExact "Hp8". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp8".
      iEval (rewrite HspP7) in "Hp8".
      set (Q1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 1 : mword 5))]> P7).
      assert (HspQ1 : Q1 !!! Regidx csp_rs1 = spd)
        by (rewrite /Q1; rewrite lookup_total_insert_ne; [ exact HspP7 | vm_compute; discriminate ]).
      assert (Hpp2a : add_vec_int (mword_of_int (PP + 0x28) : mword 64) 2 = mword_of_int (PP + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2a) in "Hpc".
      iApply (wp_cldsp_gpr_s_ram root_ppn E Φ (mword_of_int (PP + 0x2a)) (mword_of_int 0) (mword_of_int 8 : mword 5)
                Q1 (m !!! Regidx (mword_of_int 8 : mword 5))
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1) (dqm:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE
                
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2a [Hp0]").
      { iEval (rewrite HspQ1). iExact "Hp0". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hp0".
      iEval (rewrite HspQ1) in "Hp0".
      set (Q2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg (m !!! Regidx (mword_of_int 8 : mword 5))]> Q1).
      assert (Hpp2c : add_vec_int (mword_of_int (PP + 0x2a) : mword 64) 2 = mword_of_int (PP + 0x2c)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2c) in "Hpc".
      iApply (wp_caddi_gpr_s_config root_ppn E Φ (mword_of_int (PP + 0x2c)) csp_rs1 (mword_of_int 16 : mword 6) Q2
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2c [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      set (Q3 := <[Regidx csp_rs1 := regval_into_reg (add_vec (Q2 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))]> Q2).
      assert (Hpp2e : add_vec_int (mword_of_int (PP + 0x2c) : mword 64) 2 = mword_of_int (PP + 0x2e)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp2e) in "Hpc".
      assert (HraQ3 : Q3 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
      { rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /Q1. apply lookup_total_insert. }
      iApply (wp_cret_s_zca root_ppn E Φ (mword_of_int (PP + 0x2e)) (mword_of_int 1) Q3
                mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
                HN HSIE HMPRV HSXL Hmm HPBMTE  ltac:(vm_compute; discriminate) Hlpe
                ltac:(rewrite HraQ3; exact Hal0)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hi2e [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile".
      iEval (rewrite HraQ3) in "Hpc".
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                   HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm Hlpe Hfiom
                   with "Hhw Hinv Hhs Hpriv Hms Hgc Hmie Hmdl Hmenv") as "Hcfg".
      iApply ("Hcont" with "Hcfg Htlbinv Hpc [Hfile] Hnoff Hint [Hp8 Hp0 Hfra Hfs0]").
      { iExists Q3. iFrame "Hfile". iPureIntro.
        split; [exact HraQ3|]. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. apply lookup_total_insert.
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s1.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Q3. rewrite lookup_total_insert.
          assert (HspQ2 : Q2 !!! Regidx csp_rs1 = spd)
            by (rewrite /Q2; rewrite lookup_total_insert_ne; [ exact HspQ1 | vm_compute; discriminate ]).
          rewrite HspQ2.
          rewrite /spd po_addv_assoc.
          replace (add_vec (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)))
                           (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))))
            with (mword_of_int 0 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
          apply kv_addv_zero.
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_tp.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          exact Ha0P6.
        - (* s2 (x18) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s2.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s3 (x19) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s3.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s4 (x20) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s4.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
        - (* s5 (x21) *)
          rewrite /Q3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Q1. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P7. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P6. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P5. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P4. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P3. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /C po_mycpu_out_s5.
          rewrite /P2. rewrite lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /P1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate].
      }
      iExists _, _, _, _. iFrame "Hp8 Hp0 Hfra Hfs0".
  Qed.

End WpPopOffTopSec.

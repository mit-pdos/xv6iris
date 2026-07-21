(* WpSconfCpuid.v: whole-function WP for xv6's cpuid() in S-mode, over the
   SIE-agnostic sie_cap bundle.  cpuid() @ 0x800018d0 reads the thread pointer
   [tp] and returns it as an [int] (sign-extension of tp's low 32 bits):

     0x800018d0 <cpuid>:
       +0x00  1141   c.addi   sp,sp,-16     frame alloc
       +0x02  e406   c.sdsp   ra,8(sp)
       +0x04  e022   c.sdsp   s0,0(sp)
       +0x06  0800   c.addi4spn s0,sp,16
       +0x08  8512   c.mv     a0,tp         a0 = tp
       +0x0a  2501   c.addiw  a0,0          sext.w a0
       +0x0c  60a2   c.ldsp   ra,8(sp)
       +0x0e  6402   c.ldsp   s0,0(sp)
       +0x10  0141   c.addi   sp,sp,16      frame free
       +0x12  8082   c.ret

   This is a simpler [mycpu] (WpSconfMycpu.v): the SAME 16-byte frame and the
   SAME [c.mv;sext.w tp] read, but no cpus[] indexing (no slli/auipc/addi/add).
   Structure mirrors WpSconfMycpu.v leaf-by-leaf; instruction decodes for the
   shared frame ops come from KernelRvcDecode, and the two a0-flavoured decodes
   ([c.mv a0,tp], [c.addiw a0,0]) are proven here. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile WpGpr InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptTree.
Require Import StackOwn CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpDecode WpLeafCommon WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SpecCpuid.
Import Defs.

(* ---- the two a0-flavoured RVC decodes not shared with the frame set ---- *)
(* +0x08  8512  c.mv a0,tp *)
Lemma cdec_mv_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8512 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x0a  2501  c.addiw a0,0 (sext.w a0) *)
Lemma cdec_addiw_a0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2501 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 0, Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* cpuid's balanced frame: entry [addi sp,-16] and exit [addi sp,+16] cancel
   (identical to WpMycpu.mycpu_frame_cancel). *)
Lemma cpuid_frame_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64)
             = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64)
             = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

(* the [sext.w a0] result, applied to a0 = [add_vec zero_reg tp] with imm 0,
   truncates to exactly [subrange tp 31 0] -- i.e. it bridges the model's
   ADDIW value to [cpuid_ret]'s definition. *)
Lemma cpuid_addiw_bridge (X : mword 64) :
  add_vec (add_vec zero_reg X) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned.
  assert (HZ : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)) : mword 64) = 0)
    by (vm_compute; reflexivity).
  assert (HZR : bv_unsigned (zero_reg : mword 64) = 0) by (vm_compute; reflexivity).
  rewrite HZ HZR. rewrite Z.add_0_r Z.add_0_l.
  rewrite bv_wrap_bv_unsigned. apply bv_wrap_bv_unsigned.
Qed.

Module CpuidProof : CPUID.

Section WpSconfCpuid.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the ten cpuid instructions from [kernel_text].     *)
  (* Frame decodes reuse KernelRvcDecode's shared templates; the two      *)
  (* a0-reads use the local [cdec_*] lemmas above.                        *)
  (* ------------------------------------------------------------------- *)
  Lemma ci_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma ci_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma ci_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma ci_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma ci_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x08)%Z (mword_of_int 0x8512 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 10), ADD)) cdec_mv_a0 exec_execute_C_MV. Qed.

  Lemma ci_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))).
  Proof. mk_rvc (KernelSyms.cpuid + 0x0a)%Z (mword_of_int 0x2501 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10))) cdec_addiw_a0 exec_execute_C_ADDIW. Qed.

  Lemma ci_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x0c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma ci_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x0e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma ci_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x10)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma ci_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.cpuid + 0x12) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.cpuid + 0x12)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.cpuid + 0x12) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire cpuid(), entry through return.    *)
  (*  Registers: ra=x1 sp=x2 tp=x4 s0=x8 a0=x10.  On exit                 *)
  (*  a0 = cpuid_ret tp, ra/sp/s0 restored (callee-saved).                *)
  (* =================================================================== *)
  Lemma wp_cpuid_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat)
    : wp_cpuid_sconf_body γ root_ppn Φ m0 n.
  Proof.
    cbv beta delta [wp_cpuid_sconf_body].
    intros ra_idx tp_idx a0_idx pcE ra0 ret_tgt Hal0 Hn.
    (* the per-instruction register-map chain (private to the proof) *)
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a0_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2).
    set (m4 := <[Regidx a0_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> m3).
    set (m5 := <[Regidx ra_idx := regval_into_reg ra0]> m4).
    set (m6 := <[Regidx s0_idx := regval_into_reg s00]> m5).
    set (m7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hcont".
    iPoseProof (ci_00 with "Htext") as "Hi00".
    iPoseProof (ci_02 with "Htext") as "Hi02".
    iPoseProof (ci_04 with "Htext") as "Hi04".
    iPoseProof (ci_06 with "Htext") as "Hi06".
    iPoseProof (ci_08 with "Htext") as "Hi08".
    iPoseProof (ci_0a with "Htext") as "Hi0a".
    iPoseProof (ci_0c with "Htext") as "Hi0c".
    iPoseProof (ci_0e with "Htext") as "Hi0e".
    iPoseProof (ci_10 with "Htext") as "Hi10".
    iPoseProof (ci_12 with "Htext") as "Hi12".
    (* the sp geometry: sp' = pa_stk sp0 2; frame slot addresses *)
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE imm_entry m0 n 2 Hn Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    (* the two frame cells at csdsp's own address spelling *)
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x02) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x04) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,4 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x06) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: c.mv a0,tp ---- *)
    iApply (wp_cmv_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x08)) a0_idx tp_idx m2 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x08) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx))]> m2) with m3.
    (* ---- 0x0a: c.addiw a0,0 (sext.w a0) ---- *)
    iApply (wp_caddiw_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x0a)) a0_idx (mword_of_int 0 : mword 6) m3 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0a [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0a) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a0_idx := regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0))]> m3) with m4.
    (* ---- 0x0c: c.ldsp ra,8(sp) ---- *)
    assert (Hm4sp : m4 !!! Regidx csp_rs1 = sp').
    { unfold m4, m3, m2;
      repeat (rewrite upd_ne; [| vm_compute; discriminate]);
      unfold m1; rewrite upd_eq; reflexivity. }
    assert (Hpa1' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa2. }
    assert (Hra0v : m1 !!! Regidx ra_idx = ra0)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : m1 !!! Regidx s0_idx = s00)
      by (unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x0c)) (mword_of_int 1 : mword 6) ra_idx m4 (n - 2)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0c) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m4) with m5.
    (* ---- 0x0e: c.ldsp s0,0(sp) ---- *)
    assert (Hm5sp : m5 !!! Regidx csp_rs1 = m4 !!! Regidx csp_rs1)
      by (unfold m5; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hm5sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x0e)) (mword_of_int 0 : mword 6) s0_idx m5 (n - 2)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x0e) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> m5) with m6.
    (* ---- 0x10: c.addi sp,16 -- the frame pop ---- *)
    assert (Hm6sp : m6 !!! Regidx csp_rs1 = sp').
    { unfold m6, m5; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hm4sp. }
    assert (Hwv : add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite Hm6sp. unfold sp', imm_dealloc, imm_entry, sp0. apply cpuid_frame_cancel. }
    assert (Hpop : m6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv Hm6sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite Hm5sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x10)) imm_dealloc m6
              (n - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.cpuid + 0x10) : mword 64) 2 = mword_of_int (KernelSyms.cpuid + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6) with m7.
    (* ---- 0x12: c.ret ---- *)
    assert (Hm7ra : m7 !!! Regidx ra_idx = ra0).
    { unfold m7, m6; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m5. rewrite upd_eq. reflexivity. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (m7 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite Hm7ra; exact Hal0).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (KernelSyms.cpuid + 0x12)) ra_idx m7 n
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (m7 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite Hm7ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! m7 with "Hhs Hsc Hcg Htlbinv Hpc [%]").
    split.
    - assert (Hm7w : m7 = apply_writes
        [ (csp_rs1, regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))));
          (s0_idx,  regval_into_reg s00);
          (ra_idx,  regval_into_reg ra0);
          (a0_idx,  regval_into_reg (sign_extend' 64 (subrange_vec_dec (add_vec (m3 !!! Regidx a0_idx) (sign_extend' 64 (sign_extend' 12 (mword_of_int 0 : mword 6)))) 31 0)));
          (a0_idx,  regval_into_reg (add_vec zero_reg (m2 !!! Regidx tp_idx)));
          (s0_idx,  regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0))));
          (csp_rs1, regval_into_reg sp') ] m0) by reflexivity.
      rewrite Hm7w. apply callee_saved_apply_writes.
      repeat constructor.
      rewrite (outer_write_cons_eq (mword_of_int 2) csp_rs1);
        [ | vm_compute; reflexivity ].
      unfold regval_into_reg.
      rewrite Hm6sp.
      change (m0 !!! Regidx (mword_of_int 2)) with (m0 !!! Regidx csp_rs1).
      unfold sp', imm_dealloc, imm_entry.
      apply cpuid_frame_cancel.
    - rewrite /m7 /m6 /m5 /m4 /m3 /m2 /m1 /s00 /ra0.
      repeat first [ rewrite upd_eq
                   | rewrite upd_ne; [| vm_compute; discriminate] ].
      unfold cpuid_ret.
      rewrite cpuid_addiw_bridge. reflexivity.
  Qed.

  (* jal-callable form: writes ra := P+4, runs cpuid, returns to P+4. *)
  Lemma wp_call_cpuid_sconf_cs (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (P : mword 64) (jimm : mword 21)
      (m : regfile) (n : nat)
    : wp_call_cpuid_sconf_cs_body γ root_ppn Φ P jimm m n.
  Proof.
    cbv beta delta [wp_call_cpuid_sconf_cs_body].
    intros ra_idx tp_idx a0_idx m0 pcE ra0 ret_tgt Htarget Halpce Hal0 Hn.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hjal Hcont".
    iApply (wp_jal_s_sconf γ root_ppn Φ P (mword_of_int 1) jimm m n
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Htarget; exact Halpce)
              with "Hsc Hhs Hcg Htlbinv Hpc Hjal [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    iEval (rewrite Htarget) in "Hpc".
    iApply (wp_cpuid_sconf γ root_ppn Φ m0 n Hal0 Hn
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [-]").
    iIntros (m') "Hhs Hsc Hcg Htlbinv Hpc %Hcs".
    iApply ("Hcont" $! m' with "Hhs Hsc Hcg Htlbinv Hpc [%]").
    destruct Hcs as [Hcs Ha0].
    split.
    - eapply callee_saved_trans; [ | exact Hcs ].
      assert (Hm0w : m0 = apply_writes
        [ ((mword_of_int 1 : mword 5), regval_into_reg (add_vec_int P 4)) ] m) by reflexivity.
      rewrite Hm0w. apply callee_saved_apply_writes. repeat constructor.
    - rewrite Ha0. f_equal.
    all: reg_lookup.
  Qed.

End WpSconfCpuid.

End CpuidProof.

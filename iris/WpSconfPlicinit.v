(* WpSconfPlicinit.v: whole-function WP for xv6's plicinit() in S-mode, over
   the SIE-agnostic sie_cap bundle.  plicinit() @ 0x8000547e sets the PLIC
   source priorities of the UART and VIRTIO interrupts to 1:

     0x8000547e <plicinit>:
       +0x00  1141      c.addi   sp,sp,-16     frame alloc  (== cpuid/mycpu)
       +0x02  e406      c.sdsp   ra,8(sp)
       +0x04  e022      c.sdsp   s0,0(sp)
       +0x06  0800      c.addi4spn s0,sp,16
       +0x08  0c000737  lui      a4,0xc000     a4 = PLIC base 0x0c000000
       +0x0c  4785      c.li     a5,1
       +0x0e  d71c      c.sw     a5,40(a4)     *(PLIC+40)=1  (source 10 prio)
       +0x10  c35c      c.sw     a5,4(a4)      *(PLIC+4)=1   (source 1  prio)
       +0x12  60a2      c.ldsp   ra,8(sp)      frame free   (== cpuid/mycpu)
       +0x14  6402      c.ldsp   s0,0(sp)
       +0x16  0141      c.addi   sp,sp,16
       +0x18  8082      c.ret

   The 16-byte frame is byte-identical to cpuid (WpSconfCpuid.v): the prologue
   push/save and epilogue restore/pop reuse the shared KernelRvcDecode
   templates and the WpSconf{Mem,Ctl} frame leaves.  The middle is a small
   value block ([lui]/[c.li]) followed by two width-4 PLIC MMIO stores through
   [wp_sw_plic_s_sconf] (WpPlic.v), threading the raw [plic_frag] half.  *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KptPt.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpSmodeIntr.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import DevModel WpPlic SpecPlicinit.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* A closed [lo <= x < hi] bound over Z.  [lia] is unusable here: the heavy
   bitvector.tactics import installs a zify hook that answers "Cannot find
   witness" even on ground literals (durable-notes), so decide each side
   through the boolean reflection lemmas instead. *)
Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.

(* plicinit's balanced 16-byte frame: entry [addi sp,-16] and exit [addi sp,+16]
   cancel (identical to cpuid_frame_cancel / mycpu_frame_cancel). *)
Lemma plicinit_frame_cancel (X : mword 64) :
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

(* PLIC priority-branch write: an [off] in the source-priority window with a
   4-aligned offset writes source [off/4]'s priority, all other fields fixed. *)
Lemma plic_write_prio (p : plic_state) (off : Z) (src : N) (v : bv 32) :
  ((0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0))%Z = true ->
  src = Z.to_N (off / 4) ->
  plic_write p off v
  = Some (PlicState (nupd (p_prio p) src v) (p_pending p) (p_claimed p) (p_enable p) (p_thresh p)).
Proof. intros H1 H2. unfold plic_write. rewrite H1. subst src. reflexivity. Qed.

(* ---- lui a4,0xc000 (0x0c000737): 4-byte U-type decode ---- *)
Lemma pldec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* ---- creg -> reg and immediate helpers for the two c.sw sites ---- *)
Lemma pl_cr6 : creg2reg_idx (Cregidx (mword_of_int 6)) = Regidx (mword_of_int 14).
Proof. vm_compute. reflexivity. Qed.

Lemma pl_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.

Lemma pl_imm40 : zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")) = (mword_of_int 40 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma pl_imm4 : zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"00")) = (mword_of_int 4 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* +0x0c  4785  c.li a5,1 *)
Lemma pldec_li_a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4785 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x0e  d71c  c.sw a5,40(a4) *)
Lemma pldec_sw40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd71c : mword 16)) s
  = Some (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma plexec_sw40 s :
  exec (execute (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SW. cbn zeta.
  rewrite exec_returnM. rewrite pl_cr6. rewrite pl_cr7. rewrite pl_imm40. reflexivity.
Qed.

(* +0x10  c35c  c.sw a5,4(a4) *)
Lemma pldec_sw4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc35c : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma plexec_sw4 s :
  exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof.
  unfold execute. cbn match. unfold execute_C_SW. cbn zeta.
  rewrite exec_returnM. rewrite pl_cr6. rewrite pl_cr7. rewrite pl_imm4. reflexivity.
Qed.

Module PlicinitProof : PLICINIT.

Section WpSconfPlicinit.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation PL := KernelSyms.plicinit.

  (* ------------------------------------------------------------------- *)
  (* [instr] facts for the twelve plicinit instructions.                  *)
  (* Frame decodes reuse KernelRvcDecode's shared templates (byte-        *)
  (* identical to cpuid); the middle four are proven here.                *)
  (* ------------------------------------------------------------------- *)
  Lemma pi_00 : kernel_text -∗ instr (mword_of_int (PL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PL + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (PL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma pi_02 : kernel_text -∗ instr (mword_of_int (PL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PL + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma pi_04 : kernel_text -∗ instr (mword_of_int (PL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PL + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma pi_06 : kernel_text -∗ instr (mword_of_int (PL + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PL + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma pi_08 : kernel_text -∗ instr (mword_of_int (PL + 0x08) : mword 64) false (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (PL + 0x08)%Z (mword_of_int 0x0c000737 : mword 32)
    (mword_of_int (PL + 0x08) : mword 64) (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)) pldec_lui_a4. Qed.

  Lemma pi_0c : kernel_text -∗ instr (mword_of_int (PL + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (PL + 0x0c)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (PL + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) pldec_li_a5 exec_execute_C_LI. Qed.

  Lemma pi_0e : kernel_text -∗ instr (mword_of_int (PL + 0x0e) : mword 64) true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (PL + 0x0e)%Z (mword_of_int 0xd71c : mword 16)
    (mword_of_int (PL + 0x0e) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw40 plexec_sw40. Qed.

  Lemma pi_10 : kernel_text -∗ instr (mword_of_int (PL + 0x10) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (PL + 0x10)%Z (mword_of_int 0xc35c : mword 16)
    (mword_of_int (PL + 0x10) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw4 plexec_sw4. Qed.

  Lemma pi_12 : kernel_text -∗ instr (mword_of_int (PL + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PL + 0x12)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PL + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma pi_14 : kernel_text -∗ instr (mword_of_int (PL + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PL + 0x14)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PL + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma pi_16 : kernel_text -∗ instr (mword_of_int (PL + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PL + 0x16)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PL + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma pi_18 : kernel_text -∗ instr (mword_of_int (PL + 0x18) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PL + 0x18)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PL + 0x18) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) mdec_cf0 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plicinit(), entry through return.  *)
  (* =================================================================== *)
  Lemma wp_plicinit_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (p : plic_state)
    : wp_plicinit_sconf_body γ root_ppn Φ m0 n p.
  Proof.
    cbv beta delta [wp_plicinit_sconf_body].
    intros ra_idx pcE ra0 ret_tgt Hretok Hn.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 48 : mword 6)).
    set (imm_dealloc := (mword_of_int 16 : mword 6)).
    set (nzimm_s0 := (mword_of_int 4 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (m1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (m2 := <[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1).
    set (m3 := <[Regidx a4_idx := regval_into_reg (luival (mword_of_int 0xc000 : mword 20))]> m2).
    set (m4 := <[Regidx a5_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m3).
    set (m5 := <[Regidx ra_idx := regval_into_reg ra0]> m4).
    set (m6 := <[Regidx s0_idx := regval_into_reg s00]> m5).
    set (m7 := <[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6).
    (* the two PLIC states threaded through the stores *)
    set (p1 := PlicState (nupd (p_prio p) 10 (Z_to_bv 32 1)) (p_pending p) (p_claimed p) (p_enable p) (p_thresh p)).
    (* [p2] is stated over [p1]'s projections, not [p]'s, so that
       [plic_write_prio]'s conclusion unifies with it syntactically. *)
    set (p2 := PlicState (nupd (p_prio p1) 1 (Z_to_bv 32 1)) (p_pending p1) (p_claimed p1) (p_enable p1) (p_thresh p1)).
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hp Hcont".
    iPoseProof (pi_00 with "Htext") as "Hi00".
    iPoseProof (pi_02 with "Htext") as "Hi02".
    iPoseProof (pi_04 with "Htext") as "Hi04".
    iPoseProof (pi_06 with "Htext") as "Hi06".
    iPoseProof (pi_08 with "Htext") as "Hi08".
    iPoseProof (pi_0c with "Htext") as "Hi0c".
    iPoseProof (pi_0e with "Htext") as "Hi0e".
    iPoseProof (pi_10 with "Htext") as "Hi10".
    iPoseProof (pi_12 with "Htext") as "Hi12".
    iPoseProof (pi_14 with "Htext") as "Hi14".
    iPoseProof (pi_16 with "Htext") as "Hi16".
    iPoseProof (pi_18 with "Htext") as "Hi18".
    assert (Hcsp1 : m1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : sp' = pa_stk (m0 !!! Regidx csp_rs1) 2).
    { unfold sp', pa_stk, add_vec_int, imm_entry.
      apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-16 -- the frame push ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ root_ppn Φ pcE imm_entry m0 n 2 Hn Hpush
              with "Hsc Hhs Hcg Htlbinv Hpc Hi00 [-]").
    iIntros "Hhs Hsc Hcg Hframe Htlbinv Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PL + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    iDestruct (stack_own_2_elim with "Hframe") as (vr24 vs16) "[Hbra Hbs0]".
    assert (Hpa1 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hpa2 : add_vec (m1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hpa1) in "Hbra".
    iEval (rewrite -Hpa2) in "Hbs0".
    (* ---- 0x02: c.sdsp ra,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24
              with "Hsc Hhs Hcg Htlbinv Hpc Hi02 Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (PL + 0x02) : mword 64) 2 = mword_of_int (PL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16
              with "Hsc Hhs Hcg Htlbinv Hpc Hi04 Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (PL + 0x04) : mword 64) 2 = mword_of_int (PL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi06 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (PL + 0x06) : mword 64) 2 = mword_of_int (PL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: lui a4,0xc000 ---- *)
    iApply (wp_lui_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x08)) a4_idx (mword_of_int 0xc000 : mword 20)
              (luival (mword_of_int 0xc000 : mword 20)) m2 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi08 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (PL + 0x08) : mword 64) 4 = mword_of_int (PL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (luival (mword_of_int 0xc000 : mword 20))]> m2) with m3.
    (* ---- 0x0c: c.li a5,1 ---- *)
    iApply (wp_cli_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x0c)) a5_idx (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) m3 (n - 2)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate) eq_refl
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0c [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (PL + 0x0c) : mword 64) 2 = mword_of_int (PL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m3) with m4.
    (* the concrete a4/a5 values in m4 *)
    assert (Ha4 : m4 !!! Regidx a4_idx = mword_of_int 0x0c000000).
    { unfold m4. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m3. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Ha5 : m4 !!! Regidx a5_idx = mword_of_int 1).
    { unfold m4. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Hsw : (autocast (T := mword) (subrange_vec_dec (m4 !!! Regidx a5_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = Z_to_bv 32 1).
    { rewrite Ha5. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x0e: c.sw a5,40(a4)  -- source 10 priority ---- *)
    iApply (wp_sw_plic_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x0e)) true a5_idx a4_idx (mword_of_int 40) m4 (n - 2)%nat p p1
              ltac:(rewrite Ha4; zrange_vm)
              ltac:(rewrite Ha4; vm_compute; reflexivity)
              ltac:(rewrite Ha4; vm_compute; reflexivity)
              ltac:(rewrite Ha4; unfold kpt_dev_vpn; zrange_vm)
              ltac:(rewrite Ha4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Ha4; rewrite Hsw; apply plic_write_prio; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi0e Hp").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hp".
    assert (Hpp10 : add_vec_int (mword_of_int (PL + 0x0e) : mword 64) 2 = mword_of_int (PL + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* the store word from p1 (same register map m4) *)
    assert (Hsw2 : (autocast (T := mword) (subrange_vec_dec (m4 !!! Regidx a5_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = Z_to_bv 32 1) by exact Hsw.
    (* ---- 0x10: c.sw a5,4(a4)  -- source 1 priority ---- *)
    iApply (wp_sw_plic_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x10)) true a5_idx a4_idx (mword_of_int 4) m4 (n - 2)%nat p1 p2
              ltac:(rewrite Ha4; zrange_vm)
              ltac:(rewrite Ha4; vm_compute; reflexivity)
              ltac:(rewrite Ha4; vm_compute; reflexivity)
              ltac:(rewrite Ha4; unfold kpt_dev_vpn; zrange_vm)
              ltac:(rewrite Ha4; apply bv_eq; vm_compute; reflexivity)
              ltac:(rewrite Ha4; rewrite Hsw2; apply plic_write_prio; vm_compute; reflexivity)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi10 Hp").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hp".
    assert (Hpp12 : add_vec_int (mword_of_int (PL + 0x10) : mword 64) 2 = mword_of_int (PL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* collapse p2 = plicinit_plic p *)
    assert (Hp2 : p2 = plicinit_plic p).
    { unfold p2, p1, plicinit_plic, uart_irq_id, virtio_irq_id. reflexivity. }
    iEval (rewrite Hp2) in "Hp".
    (* ---- 0x12: c.ldsp ra,8(sp) ---- *)
    assert (Hm4sp : m4 !!! Regidx csp_rs1 = sp').
    { unfold m4, m3, m2. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m1. rewrite upd_eq. reflexivity. }
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
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x12)) (mword_of_int 1 : mword 6) ra_idx m4 (n - 2)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi12 Hbra [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbra".
    assert (Hpp14 : add_vec_int (mword_of_int (PL + 0x12) : mword 64) 2 = mword_of_int (PL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m4) with m5.
    (* ---- 0x14: c.ldsp s0,0(sp) ---- *)
    assert (Hm5sp : m5 !!! Regidx csp_rs1 = m4 !!! Regidx csp_rs1)
      by (unfold m5; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hm5sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x14)) (mword_of_int 0 : mword 6) s0_idx m5 (n - 2)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hsc Hhs Hcg Htlbinv Hpc Hi14 Hbs0 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc Hbs0".
    assert (Hpp16 : add_vec_int (mword_of_int (PL + 0x14) : mword 64) 2 = mword_of_int (PL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> m5) with m6.
    (* ---- 0x16: c.addi sp,16 -- the frame pop ---- *)
    assert (Hm6sp : m6 !!! Regidx csp_rs1 = sp').
    { unfold m6, m5; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hm4sp. }
    assert (Hwv : add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite Hm6sp. unfold sp', imm_dealloc, imm_entry, sp0. apply plicinit_frame_cancel. }
    assert (Hpop : m6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv Hm6sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite Hm5sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x16)) imm_dealloc m6
              (n - 2)%nat 2 Hpop
              with "Hsc Hhs Hcg Htlbinv Hpc Hi16 Hframe [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp18 : add_vec_int (mword_of_int (PL + 0x16) : mword 64) 2 = mword_of_int (PL + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6) with m7.
    (* ---- 0x18: c.ret ---- *)
    assert (Hm7ra : m7 !!! Regidx ra_idx = ra0).
    { unfold m7, m6; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m5. rewrite upd_eq. reflexivity. }
    assert (Hal0' : eq_vec (access_vec_dec (update_vec_dec (add_vec (m7 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true)
      by (rewrite Hm7ra; exact Hretok).
    iApply (wp_cret_s_sconf γ root_ppn Φ (mword_of_int (PL + 0x18)) ra_idx m7 n
              ltac:(vm_compute; discriminate) Hal0'
              with "Hsc Hhs Hcg Htlbinv Hpc Hi18 [-]").
    iIntros "Hhs Hsc Hcg Htlbinv Hpc".
    assert (Hra_final : update_vec_dec (add_vec (m7 !!! Regidx ra_idx) (sign_extend' 64 (zeros' 12))) 0 ('b"0") = ret_tgt)
      by (rewrite Hm7ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! m7 with "Hhs Hsc Hcg Htlbinv Hpc [%] Hp").
    split.
    - assert (Hm7w : m7 = apply_writes
        [ (csp_rs1, regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))));
          (s0_idx,  regval_into_reg s00);
          (ra_idx,  regval_into_reg ra0);
          (a5_idx,  regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))));
          (a4_idx,  regval_into_reg (luival (mword_of_int 0xc000 : mword 20)));
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
      apply plicinit_frame_cancel.
    - exact Hm7ra.
  Qed.

End WpSconfPlicinit.

End PlicinitProof.

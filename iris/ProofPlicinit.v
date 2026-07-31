(* ProofPlicinit.v: whole-function WP for xv6's plicinit() in S-mode, over
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

   The 16-byte frame is byte-identical to cpuid (ProofCpuid.v): the prologue
   push/save and epilogue restore/pop reuse the shared KernelRvcDecode
   templates and the Proof{Mem,Ctl} frame leaves.  The middle is a small
   value block ([lui]/[c.li]) followed by two width-4 PLIC MMIO stores.

   THE TWO STORES GO THROUGH THE INVARIANT-BORROWING LEAF
   [wp_sw_plic_pinv_s_sconf] (WpPlic.v), which opens [plic_inv] across each
   (atomic) write.  This is what the re-statement of the contract over the
   time-0 device invariant bought and cost: plicinit no longer owns
   [plic_frag], so it cannot say WHAT the PLIC state becomes -- it can only
   discharge the leaf's universal obligation "the write is defined and
   preserves [plic_ok] at every admissible state".  For a source-PRIORITY
   write that is exactly [PlicPlan.plic_write_prio_ok]: the priority window's
   branch of [plic_write] is total, and it touches only [p_prio], which the
   plan does not constrain.  So there is no ghost step at all here, and
   nothing about the PLIC comes back to the caller. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import RegFile InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import HartTp WpNext IntrDefs.
Require Import KptPt.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpSmodeIntr.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import PlicPlan WpPlic SpecPlicinit.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* A closed [lo <= x < hi] bound over Z.  [lia] is unusable here: the heavy
   bitvector.tactics import installs a zify hook that answers "Cannot find
   witness" even on ground literals (durable-notes), so decide each side
   through the boolean reflection lemmas instead. *)
Ltac zrange_vm := split; [ apply Z.leb_le | apply Z.ltb_lt ]; vm_compute; reflexivity.

(* ---- lui a4,0xc000 (0x0c000737): 4-byte U-type decode ---- *)
Lemma pldec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c000737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* ---- creg -> reg and immediate helpers for the two c.sw sites ---- *)
(* +0x0e  d71c  c.sw a5,40(a4) *)
Lemma pldec_sw40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd71c : mword 16)) s
  = Some (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma plexec_sw40 s :
  exec (execute (C_SW (mword_of_int 10, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* +0x10  c35c  c.sw a5,4(a4) *)
Lemma pldec_sw4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc35c : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma plexec_sw4 s :
  exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module PlicinitProof : PLICINIT.

Section ProofPlicinit.
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
    (mword_of_int (PL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma pi_02 : kernel_text -∗ instr (mword_of_int (PL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PL + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma pi_04 : kernel_text -∗ instr (mword_of_int (PL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PL + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma pi_06 : kernel_text -∗ instr (mword_of_int (PL + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PL + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma pi_08 : kernel_text -∗ instr (mword_of_int (PL + 0x08) : mword 64) false (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (PL + 0x08)%Z (mword_of_int 0x0c000737 : mword 32)
    (mword_of_int (PL + 0x08) : mword 64) (UTYPE (mword_of_int 0xc000 : mword 20, Regidx (mword_of_int 14), LUI)) pldec_lui_a4. Qed.

  Lemma pi_0c : kernel_text -∗ instr (mword_of_int (PL + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (PL + 0x0c)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (PL + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma pi_0e : kernel_text -∗ instr (mword_of_int (PL + 0x0e) : mword 64) true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (PL + 0x0e)%Z (mword_of_int 0xd71c : mword 16)
    (mword_of_int (PL + 0x0e) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw40 plexec_sw40. Qed.

  Lemma pi_10 : kernel_text -∗ instr (mword_of_int (PL + 0x10) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (PL + 0x10)%Z (mword_of_int 0xc35c : mword 16)
    (mword_of_int (PL + 0x10) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) pldec_sw4 plexec_sw4. Qed.

  Lemma pi_12 : kernel_text -∗ instr (mword_of_int (PL + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PL + 0x12)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PL + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma pi_14 : kernel_text -∗ instr (mword_of_int (PL + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PL + 0x14)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PL + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma pi_16 : kernel_text -∗ instr (mword_of_int (PL + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PL + 0x16)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PL + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma pi_18 : kernel_text -∗ instr (mword_of_int (PL + 0x18) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PL + 0x18)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PL + 0x18) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plicinit(), entry through return.  *)
  (* =================================================================== *)
  Lemma wp_plicinit_sconf (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (b : bool) (p : mword 64)
    : wp_plicinit_sconf_body Φ m0 n b p.
  Proof.
    cbv beta delta [wp_plicinit_sconf_body].
    intros ra_idx pcE ra0 ret_tgt Hn.
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
    iIntros "Hcg #Htext Hpc #Hpinv Hcont".
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
    iApply (wp_caddi_sp_push_s_sconf Φ pcE imm_entry m0 n 2 b Hn Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
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
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PL + 0x02)) (mword_of_int 1 : mword 6) ra_idx m1 (n - 2)%nat vr24 b
              with "Hcg Hpc Hi02 Hbra [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hbra".
    assert (Hpp04 : add_vec_int (mword_of_int (PL + 0x02) : mword 64) 2 = mword_of_int (PL + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,0(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PL + 0x04)) (mword_of_int 0 : mword 6) s0_idx m1 (n - 2)%nat vs16 b
              with "Hcg Hpc Hi04 Hbs0 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hbs0".
    assert (Hpp06 : add_vec_int (mword_of_int (PL + 0x04) : mword 64) 2 = mword_of_int (PL + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.addi4spn s0,sp,16 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PL + 0x06)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx m1 (n - 2)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi06 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc".
    assert (Hpp08 : add_vec_int (mword_of_int (PL + 0x06) : mword 64) 2 = mword_of_int (PL + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (m1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> m1) with m2.
    (* ---- 0x08: lui a4,0xc000 ---- *)
    iApply (wp_lui_s_sconf Φ (mword_of_int (PL + 0x08)) a4_idx (mword_of_int 0xc000 : mword 20)
              (luival (mword_of_int 0xc000 : mword 20)) m2 (n - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (PL + 0x08) : mword 64) 4 = mword_of_int (PL + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (luival (mword_of_int 0xc000 : mword 20))]> m2) with m3.
    (* ---- 0x0c: c.li a5,1 ---- *)
    iApply (wp_cli_s_sconf Φ (mword_of_int (PL + 0x0c)) a5_idx (mword_of_int 1 : mword 6)
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) m3 (n - 2)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok) eq_refl
              with "Hcg Hpc Hi0c [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hpp0e : add_vec_int (mword_of_int (PL + 0x0c) : mword 64) 2 = mword_of_int (PL + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6))))]> m3) with m4.
    (* the concrete a4/a5 values in m4 *)
    assert (Ha4 : m4 !!! Regidx a4_idx = mword_of_int 0x0c000000).
    { unfold m4. rewrite upd_ne; [| vm_compute; discriminate].
      unfold m3. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    assert (Ha5 : m4 !!! Regidx a5_idx = mword_of_int 1).
    { unfold m4. rewrite upd_eq. apply bv_eq; vm_compute; reflexivity. }
    (* the leaves' [ea]/[storeword] now read the a4/a5 registers via [rget]
       (they sit at a VARIABLE index) -- bridge from the plain map facts.
       Stated generically over the hart: at this point in a [b]-GENERIC
       proof the ambient hart is an ABSTRACT [wp_next]-bound variable (CID6
       below), not the section's outer [CID], so a fact tied to one
       particular instance would not [rewrite] into a leaf application that
       unifies its implicit hart from a DIFFERENT resource (here, [Hcg] at
       CID6) -- quantify over the hart instead, exactly as [rget_ne] does. *)
    assert (Ha4' : forall (CID' : CpuId), rget (CID := CID') m4 a4_idx = mword_of_int 0x0c000000)
      by (intros CID'; rgne; exact Ha4).
    assert (Ha5' : forall (CID' : CpuId), rget (CID := CID') m4 a5_idx = mword_of_int 1)
      by (intros CID'; rgne; exact Ha5).
    assert (Hsw : forall (CID' : CpuId),
              (autocast (T := mword) (subrange_vec_dec (rget (CID := CID') m4 a5_idx) (Z.sub (Z.mul 4 8) 1) 0) : mword 32) = Z_to_bv 32 1).
    { intros CID'. rewrite (Ha5' CID'). apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x0e: c.sw a5,40(a4)  -- source 10 priority ----
       [(CID := CID6)] is explicit: the ltac: side-condition arguments below
       elaborate BEFORE the "with" clause unifies the leaf's implicit hart
       against [Hcg], so left implicit it is still a bare evar when [Ha4']
       tries to [rewrite] into it ("does not match any subterm" against
       [rget ?CID m4 a4_idx]) -- pin it to the hart [Hcg] is actually at. *)
    iApply (wp_sw_plic_pinv_s_sconf (CID := CID6) Φ (mword_of_int (PL + 0x0e)) true a5_idx a4_idx (mword_of_int 40) m4 (n - 2)%nat b
              ltac:(rewrite Ha4'; zrange_vm)
              ltac:(rewrite Ha4'; vm_compute; reflexivity)
              ltac:(rewrite Ha4'; vm_compute; reflexivity)
              ltac:(rewrite Ha4'; unfold kpt_dev_vpn; zrange_vm)
              ltac:(rewrite Ha4' Hsw; intros pq Hpq; apply plic_write_prio_ok;
                    [ vm_compute; reflexivity | exact Hpq ])
              with "Hcg Hpc Hi0e Hpinv").
    iIntros (CID7 Hs7) "Hcg Hpc".
    assert (Hpp10 : add_vec_int (mword_of_int (PL + 0x0e) : mword 64) 2 = mword_of_int (PL + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    (* ---- 0x10: c.sw a5,4(a4)  -- source 1 priority ---- *)
    iApply (wp_sw_plic_pinv_s_sconf (CID := CID7) Φ (mword_of_int (PL + 0x10)) true a5_idx a4_idx (mword_of_int 4) m4 (n - 2)%nat b
              ltac:(rewrite Ha4'; zrange_vm)
              ltac:(rewrite Ha4'; vm_compute; reflexivity)
              ltac:(rewrite Ha4'; vm_compute; reflexivity)
              ltac:(rewrite Ha4'; unfold kpt_dev_vpn; zrange_vm)
              ltac:(rewrite Ha4' Hsw; intros pq Hpq; apply plic_write_prio_ok;
                    [ vm_compute; reflexivity | exact Hpq ])
              with "Hcg Hpc Hi10 Hpinv").
    iIntros (CID8 Hs8) "Hcg Hpc".
    assert (Hpp12 : add_vec_int (mword_of_int (PL + 0x10) : mword 64) 2 = mword_of_int (PL + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    (* ---- 0x12: c.ldsp ra,8(sp) ---- *)
    assert (Hm4sp : m4 !!! Regidx csp_rs1 = sp').
    { unfold m4, m3, m2. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m1. rewrite upd_eq. reflexivity. }
    assert (Hpa1' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa1. }
    assert (Hpa2' : add_vec (m4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hm4sp. rewrite -Hcsp1. exact Hpa2. }
    (* generic over the hart, same reason as [Ha4'] above: "Hbra"/"Hbs0" are
       concrete at whichever hart the c.sdsp steps landed on, and a fact tied
       to one arbitrarily-picked instance would not [rewrite] into them. *)
    assert (Hra0v : forall (CID' : CpuId), rget (CID := CID') m1 ra_idx = ra0)
      by (intros CID'; rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : forall (CID' : CpuId), rget (CID := CID') m1 s0_idx = s00)
      by (intros CID'; rgne; unfold m1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hpa1 -Hpa1' Hra0v) in "Hbra".
    iEval (rewrite Hpa2 -Hpa2' Hs00v) in "Hbs0".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PL + 0x12)) (mword_of_int 1 : mword 6) ra_idx m4 (n - 2)%nat ra0 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi12 Hbra [-]").
    iIntros (CID9 Hs9) "Hcg Hpc Hbra".
    assert (Hpp14 : add_vec_int (mword_of_int (PL + 0x12) : mword 64) 2 = mword_of_int (PL + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> m4) with m5.
    (* ---- 0x14: c.ldsp s0,0(sp) ---- *)
    assert (Hm5sp : m5 !!! Regidx csp_rs1 = m4 !!! Regidx csp_rs1)
      by (unfold m5; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -Hm5sp) in "Hbs0".
    iApply (wp_cldsp_s_sconf Φ (mword_of_int (PL + 0x14)) (mword_of_int 0 : mword 6) s0_idx m5 (n - 2)%nat s00 b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi14 Hbs0 [-]").
    iIntros (CID10 Hs10) "Hcg Hpc Hbs0".
    assert (Hpp16 : add_vec_int (mword_of_int (PL + 0x14) : mword 64) 2 = mword_of_int (PL + 0x16)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp16) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> m5) with m6.
    (* ---- 0x16: c.addi sp,16 -- the frame pop ---- *)
    assert (Hm6sp : m6 !!! Regidx csp_rs1 = sp').
    { unfold m6, m5; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      exact Hm4sp. }
    assert (Hwv : add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)) = sp0).
    { rewrite Hm6sp. unfold sp', imm_dealloc, imm_entry, sp0. apply frame_cancel_16. }
    assert (Hpop : m6 !!! Regidx csp_rs1
                   = pa_stk (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc))) 2).
    { rewrite Hwv Hm6sp. exact Hpush. }
    iEval (rewrite Hpa1') in "Hbra".
    iEval (rewrite Hm5sp Hpa2') in "Hbs0".
    iDestruct (stack_own_2_intro sp0 with "Hbra Hbs0") as "Hframe".
    iEval (rewrite -Hwv) in "Hframe".
    iApply (wp_caddi_sp_pop_s_sconf Φ (mword_of_int (PL + 0x16)) imm_dealloc m6
              (n - 2)%nat 2 b Hpop
              with "Hcg Hpc Hi16 Hframe [-]").
    iIntros (CID11 Hs11) "Hcg Hpc".
    assert (Hnk : ((n - 2) + 2)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp18 : add_vec_int (mword_of_int (PL + 0x16) : mword 64) 2 = mword_of_int (PL + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (m6 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_dealloc)))]> m6) with m7.
    (* ---- 0x18: c.ret ---- *)
    assert (Hm7ra : m7 !!! Regidx ra_idx = ra0).
    { unfold m7, m6; repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold m5. rewrite upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf Φ (mword_of_int (PL + 0x18)) ra_idx m7 n b
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18 [-]").
    iIntros (CID12 Hs12) "Hcg Hpc".
    assert (Hra_final : forall (CID' : CpuId), ret_pc (rget (CID := CID') m7 ra_idx) = ret_tgt)
      by (intros CID'; rgne; rewrite Hm7ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iSpecialize ("Hcont" $! CID12 with "[%]"); [wp_next_chain|].
    iApply ("Hcont" $! m7 with "Hcg Hpc [%]").
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
      apply frame_cancel_16.
    - exact Hm7ra.
  Qed.

End ProofPlicinit.

End PlicinitProof.

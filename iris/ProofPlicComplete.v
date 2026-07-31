(* ProofPlicComplete.v: whole-function WP for xv6's plic_complete() in S-mode,
   over the SIE-agnostic sie_cap bundle.  plic_complete() @ 0x800054ec writes the
   id it is handed back to this hart's PLIC claim/complete register:

     0x800054ec <plic_complete>:
       +0x00  1101      c.addi   sp,sp,-32     frame alloc (32-byte, == kalloc)
       +0x02  ec06      c.sdsp   ra,24(sp)
       +0x04  e822      c.sdsp   s0,16(sp)
       +0x06  e426      c.sdsp   s1,8(sp)
       +0x08  1000      c.addi4spn s0,sp,32
       +0x0a  84aa      c.mv     s1,a0         save the irq argument
       +0x0c  bd8fc0ef  jal      ra,cpuid      a0 = hart id
       +0x10  00d5179b  slliw    a5,a0,0xd
       +0x14  0c201737  lui      a4,0xc201
       +0x18  97ba      c.add    a5,a5,a4      a5 = PLIC+0x201000 + hart*0x2000
       +0x1a  c3c4      c.sw     s1,4(a5)      *PLIC_SCLAIM(hart) = irq
       +0x1c  60e2      c.ldsp   ra,24(sp)     frame free
       +0x1e  6442      c.ldsp   s0,16(sp)
       +0x20  64a2      c.ldsp   s1,8(sp)
       +0x22  6105      c.addi16sp sp,32
       +0x24  8082      c.ret

   The 32-byte frame is byte-identical to kalloc's, so the prologue and
   epilogue reuse KernelRvcDecode's shared templates ([cdec_1101]..[cdec_8082])
   and the Proof{Mem,Ctl,Alu} frame leaves.  The MMIO write goes through
   [wp_sw_plic_dev_s_sconf] (WpPlic.v), which opens the device invariant across
   the (atomic) store -- every hart runs this concurrently, so none of them may
   own [plic_frag] across a step.

   The write is the model's COMPLETION: it clears a [p_claimed] bit and nothing
   else, so the kernel's PLIC plan [plic_ok] (PlicPlan.v) survives it for ANY
   value written ([plic_ok_complete]) -- which is why nothing is required of the
   irq argument.  The hart-id address arithmetic is shared with plicinithart and
   plic_claim and lives in PlicHart.v. *)
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
Require Import HartTp WpNext.
Require Import StackOwn CalleeSaved KernelText.
Require Import WpDecodeBridge.
Require Import KernelRvcDecode WpRvcBridge.
Require Import VcGen WpSconfAlu WpSconfMem WpSconfCtl.
Require Import PlicPlan PlicHart DiskPtsto WpUart WpPlic SpecCpuid SpecPlicComplete.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

(* ---- the decodes used only by plic_complete ---- *)

(* +0x0c  bd8fc0ef  jal ra,cpuid *)
Lemma pcdec_jal s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbd8fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x10  00d5179b  slliw a5,a0,0xd *)
Lemma pcdec_slliw_a5 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d5179b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* +0x14  0c201737  lui a4,0xc201 *)
Lemma pcdec_lui_a4 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0c201737 : mword 32)) s
  = Some (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  c3c4  c.sw s1,4(a5) *)
Lemma pcdec_sw_s1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc3c4 : mword 16)) s
  = Some (C_SW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma pc_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9).
Proof. vm_compute. reflexivity. Qed.
Lemma pc_imm4 : zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"00")) = (mword_of_int 4 : mword 12).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma pcexec_sw_s1 s :
  exec (execute (C_SW (mword_of_int 1, Cregidx (mword_of_int 7), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)), s).
Proof.
  rewrite exec_execute_C_SW. rewrite pc_cr7. rewrite pc_cr1. rewrite pc_imm4. reflexivity.
Qed.

(* [rget m k] at a NON-tp index is the plain map lookup ([rget_ne]) -- the
   one-line bridge from a leaf's [rget] to the register-map facts a
   whole-function proof already has.  Written name-free (durable-notes: an
   Ltac body cannot mention a hypothesis by literal name). *)
Local Ltac rgne :=
  rewrite rget_ne;
  [ | let H1 := fresh in let H2 := fresh in
      intro H1; injection H1 as H2; vm_compute in H2; congruence ].

Module PlicCompleteProof (Cpuid : CPUID) : PLIC_COMPLETE.

Section ProofPlicComplete.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{CID : CpuId}.

  Notation PC := KernelSyms.plic_complete.

  (* ---- [instr] facts for the fifteen plic_complete instructions ---- *)
  Lemma pci_00 : kernel_text -∗ instr (mword_of_int (PC + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PC + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (PC + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma pci_02 : kernel_text -∗ instr (mword_of_int (PC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PC + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (PC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma pci_04 : kernel_text -∗ instr (mword_of_int (PC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PC + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (PC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma pci_06 : kernel_text -∗ instr (mword_of_int (PC + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PC + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (PC + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma pci_08 : kernel_text -∗ instr (mword_of_int (PC + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PC + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (PC + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma pci_0a : kernel_text -∗ instr (mword_of_int (PC + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PC + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (PC + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma pci_0c : kernel_text -∗ instr (mword_of_int (PC + 0x0c) : mword 64) false (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x0c)%Z (mword_of_int 0xbd8fc0ef : mword 32)
    (mword_of_int (PC + 0x0c) : mword 64) (JAL (mword_of_int 2081752 : mword 21, Regidx (mword_of_int 1))) pcdec_jal. Qed.

  Lemma pci_10 : kernel_text -∗ instr (mword_of_int (PC + 0x10) : mword 64) false (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW)).
  Proof. mk_base (PC + 0x10)%Z (mword_of_int 0x00d5179b : mword 32)
    (mword_of_int (PC + 0x10) : mword 64) (SHIFTIWOP (mword_of_int 13 : mword 5, Regidx (mword_of_int 10), Regidx (mword_of_int 15), SLLIW)) pcdec_slliw_a5. Qed.

  Lemma pci_14 : kernel_text -∗ instr (mword_of_int (PC + 0x14) : mword 64) false (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (PC + 0x14)%Z (mword_of_int 0x0c201737 : mword 32)
    (mword_of_int (PC + 0x14) : mword 64) (UTYPE (mword_of_int 0xc201 : mword 20, Regidx (mword_of_int 14), LUI)) pcdec_lui_a4. Qed.

  Lemma pci_18 : kernel_text -∗ instr (mword_of_int (PC + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PC + 0x18)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (PC + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma pci_1a : kernel_text -∗ instr (mword_of_int (PC + 0x1a) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (PC + 0x1a)%Z (mword_of_int 0xc3c4 : mword 16)
    (mword_of_int (PC + 0x1a) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), 4)) pcdec_sw_s1 pcexec_sw_s1. Qed.

  Lemma pci_1c : kernel_text -∗ instr (mword_of_int (PC + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PC + 0x1c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (PC + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma pci_1e : kernel_text -∗ instr (mword_of_int (PC + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PC + 0x1e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (PC + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma pci_20 : kernel_text -∗ instr (mword_of_int (PC + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PC + 0x20)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (PC + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma pci_22 : kernel_text -∗ instr (mword_of_int (PC + 0x22) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PC + 0x22)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (PC + 0x22) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma pci_24 : kernel_text -∗ instr (mword_of_int (PC + 0x24) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PC + 0x24)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PC + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* =================================================================== *)
  (*  THE CAPSTONE: a WP for the entire plic_complete(), entry to return. *)
  (* =================================================================== *)
  (* BLOCKED.  Ported up through the [c.mv s1,a0] that saves the irq
     argument; the very next instruction is [jal cpuid], and that call
     cannot be discharged against [SpecPlicComplete.v]'s (already-ported,
     out-of-scope) contract -- see the [Fail] below and the comment at it.
     Everything up to there compiles and is genuinely the ported shape
     (leaf-by-leaf, [rd_ok] -> [ltac:(rdok)], per-leaf [wp_next] peeled with
     [iIntros (CIDk Hsk) "…"], exactly the generic-[b] template). *)
  Lemma wp_plic_complete_sconf (γd : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (b : bool)
    : wp_plic_complete_sconf_body γd γv Φ m0 n b.
  Proof.
    cbv beta delta [wp_plic_complete_sconf_body].
    intros ra_idx tp_idx pcE ra0 ret_tgt Hhart Hn.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (s1_idx := (mword_of_int 9 : mword 5)).
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 32 : mword 6)).
    set (nzimm_s0 := (mword_of_int 8 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (s10 := m0 !!! Regidx s1_idx).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (R2 := <[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1).
    iIntros "Hcg #Htext Hpc #Hdinv Hcont".
    iPoseProof (pci_00 with "Htext") as "Hi00".
    iPoseProof (pci_02 with "Htext") as "Hi02".
    iPoseProof (pci_04 with "Htext") as "Hi04".
    iPoseProof (pci_06 with "Htext") as "Hi06".
    iPoseProof (pci_08 with "Htext") as "Hi08".
    iPoseProof (pci_0a with "Htext") as "Hi0a".
    iPoseProof (pci_0c with "Htext") as "Hi0c".
    assert (Hn4 : (4 <= n)%nat) by lia.
    assert (Hcsp1 : R1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))
                    = pa_stk (m0 !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int, imm_entry. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-32 -- the frame push (k := 4) ---- *)
    iApply (wp_caddi_sp_push_s_sconf Φ pcE imm_entry m0 n 4 b Hn4 Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros (CID1 Hs1) "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PC + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)))]> m0) with R1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PC + 0x02)) (mword_of_int 3 : mword 6) ra_idx R1 (n - 4)%nat vr24 b
              with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros (CID2 Hs2) "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PC + 0x02) : mword 64) 2 = mword_of_int (PC + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PC + 0x04)) (mword_of_int 2 : mword 6) s0_idx R1 (n - 4)%nat vr16 b
              with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros (CID3 Hs3) "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PC + 0x04) : mword 64) 2 = mword_of_int (PC + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf Φ (mword_of_int (PC + 0x06)) (mword_of_int 1 : mword 6) s1_idx R1 (n - 4)%nat vr8 b
              with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros (CID4 Hs4) "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PC + 0x06) : mword 64) 2 = mword_of_int (PC + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf Φ (mword_of_int (PC + 0x08)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx R1 (n - 4)%nat b
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi08 [-]").
    iIntros (CID5 Hs5) "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (PC + 0x08) : mword 64) 2 = mword_of_int (PC + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1) with R2.
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf Φ (mword_of_int (PC + 0x0a)) s1_idx a0_idx R2 (n - 4)%nat b
              ltac:(vm_compute; discriminate) ltac:(rdok)
              with "Hcg Hpc Hi0a [-]").
    iIntros (CID6 Hs6) "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (PC + 0x0a) : mword 64) 2 = mword_of_int (PC + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    set (R3 := <[Regidx s1_idx := regval_into_reg (add_vec zero_reg (rget (CID := CID6) R2 a0_idx))]> R2).
    change (<[Regidx s1_idx := regval_into_reg (add_vec zero_reg (rget (CID := CID6) R2 a0_idx))]> R2) with R3.
    assert (HR3sp : R3 !!! Regidx csp_rs1 = sp').
    { unfold R3, R2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hcsp1. }
    (* ---- 0x0c: jal ra,cpuid ----

       BLOCKED HERE, for the same reason already diagnosed at
       ProofPlicClaim.v:228-267 and ProofPlicinithart.v (both mid-port on
       this same branch, both hitting the identical gap on their own
       unbracketed [jal cpuid]): [Cpuid.wp_call_cpuid_sconf_cs] fixes the
       callee's SIE state to the LITERAL [false] -- it carries no [b] binder
       at all, per the "a function that reads tp mid-body must be stated at
       b = false" rule (cpuid's own [c.mv a0,tp]).  But plic_complete's own
       contract (SpecPlicComplete.v, already ported, out of scope for this
       sweep) is [b]-GENERIC: it threads [sie_cap_gpr _ n b] unchanged from
       entry to exit through a [wp_next b] wrapper, and plic_complete's code
       -- like plic_claim's and plicinithart's -- contains NO
       push_off/pop_off bracket that could turn an arbitrary entry [b] into
       a proved [false] before this call. At this point the only resource in
       hand is [Hcg : sie_cap_gpr R3 (n - 4) b] for an ARBITRARY bound [b],
       which does not even syntactically match the callee's required
       [sie_cap_gpr R3 (n - 4) false], and there is no lemma in
       IntrDefs.v/WpNext.v that converts one to the other (nor could there
       be: [sie_arm] ties each arm to a DIFFERENT, mutually exclusive value
       of the SIE ghost variable, so producing [false] from a held [b] is a
       real ghost-state update, not a reformulation, and nothing in
       plic_complete's instruction stream performs one). The physical
       reading is the same as at the sibling files: if plic_complete
       genuinely ran with interrupts enabled, a timer interrupt could fire
       during cpuid's own [c.mv a0,tp; sext.w a0] and hand back neither
       hart's id -- exactly what cpuid's contract exists to rule out, and
       nothing in plic_complete's own body prevents it. (In the real xv6,
       plic_complete is only ever called from devintr(), itself reached from
       {user,kernel}trap() before interrupts are turned back on -- so it is
       always run at b = false in practice, and that fact needs to be
       reflected in the contract, not manufactured here.)

       This is a THIRD confirmed instance of the same (out-of-scope,
       already-ported, already-green) Spec gap: any function whose C body
       calls cpuid()/mycpu() without its own push_off/pop_off bracket cannot
       be [b]-generic, and SpecPlicComplete.v should almost certainly drop
       its [wp_next] wrapper and be stated at [b = false] only, exactly like
       SpecCpuid/SpecMycpu/(most likely) SpecPlicinithart/SpecPlicClaim. Per
       the porting instructions this is a case to report rather than force,
       so the call site below is left as the literal (as-if-b-generic)
       attempt and the proof is [Abort]ed rather than closed with a
       fabricated or weakened statement. *)
    Fail iApply (Cpuid.wp_call_cpuid_sconf_cs Φ (mword_of_int (PC + 0x0c))
              (mword_of_int 2081752 : mword 21) R3 (n - 4)%nat
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi0c [-]").
  Abort.
(* -----------------------------------------------------------------------
   Everything below this point is the OLD (pre-port) continuation of the
   proof, kept verbatim for reference (it is dead code: the [Abort] above
   means [wp_plic_complete_sconf] is not defined, and the enclosing functor
   application below will fail to close for that reason alone -- exactly the
   state ProofPlicClaim.v / ProofPlicinithart.v are already in for the
   identical reason). It shows the shape the rest of the port would take if
   SpecPlicComplete.v's [b] binder were resolved (most likely by stating it
   at [b = false] only, per the note above): with [rget]/[rget_tp] the
   [HR3tp] bridge below collapses, because [rget _ tp_idx] is [cid_word] at
   ANY map.

  Lemma wp_plic_complete_sconf (γ : gname) (γd : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat)
    : wp_plic_complete_sconf_body γ γd γv Φ m0 n.
  Proof.
    cbv beta delta [wp_plic_complete_sconf_body].
    intros ra_idx tp_idx pcE ra0 ret_tgt Hhart Hn.
    set (s0_idx := (mword_of_int 8 : mword 5)).
    set (s1_idx := (mword_of_int 9 : mword 5)).
    set (a0_idx := (mword_of_int 10 : mword 5)).
    set (a4_idx := (mword_of_int 14 : mword 5)).
    set (a5_idx := (mword_of_int 15 : mword 5)).
    set (imm_entry := (mword_of_int 32 : mword 6)).
    set (nzimm_s0 := (mword_of_int 8 : mword 8)).
    set (sp0 := m0 !!! Regidx csp_rs1).
    set (sp' := add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))).
    set (s00 := m0 !!! Regidx s0_idx).
    set (s10 := m0 !!! Regidx s1_idx).
    set (R1 := <[Regidx csp_rs1 := regval_into_reg sp']> m0).
    set (R2 := <[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1).
    set (R3 := <[Regidx s1_idx := regval_into_reg (add_vec zero_reg (R2 !!! Regidx a0_idx))]> R2).
    iIntros "Hcg #Htext Hpc #Hdinv Hcont".
    iPoseProof (pci_00 with "Htext") as "Hi00".
    iPoseProof (pci_02 with "Htext") as "Hi02".
    iPoseProof (pci_04 with "Htext") as "Hi04".
    iPoseProof (pci_06 with "Htext") as "Hi06".
    iPoseProof (pci_08 with "Htext") as "Hi08".
    iPoseProof (pci_0a with "Htext") as "Hi0a".
    iPoseProof (pci_0c with "Htext") as "Hi0c".
    iPoseProof (pci_10 with "Htext") as "Hi10".
    iPoseProof (pci_14 with "Htext") as "Hi14".
    iPoseProof (pci_18 with "Htext") as "Hi18".
    iPoseProof (pci_1a with "Htext") as "Hi1a".
    iPoseProof (pci_1c with "Htext") as "Hi1c".
    iPoseProof (pci_1e with "Htext") as "Hi1e".
    iPoseProof (pci_20 with "Htext") as "Hi20".
    iPoseProof (pci_22 with "Htext") as "Hi22".
    iPoseProof (pci_24 with "Htext") as "Hi24".
    assert (Hn4 : (4 <= n)%nat) by lia.
    assert (Hcsp1 : R1 !!! Regidx csp_rs1 = sp') by (apply upd_eq).
    assert (Hpush : add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry))
                    = pa_stk (m0 !!! Regidx csp_rs1) 4).
    { unfold pa_stk, add_vec_int, imm_entry. apply f_equal. apply bv_eq; vm_compute; reflexivity. }
    (* ---- 0x00: c.addi sp,-32 -- the frame push (k := 4) ---- *)
    iApply (wp_caddi_sp_push_s_sconf γ Φ pcE imm_entry m0 n 4 Hn4 Hpush
              with "Hcg Hpc Hi00 [-]").
    iIntros "Hcg Hframe Hpc".
    assert (Hpp02 : add_vec_int (pcE : mword 64) 2 = mword_of_int (PC + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg
        (add_vec (m0 !!! Regidx csp_rs1) (sign_extend' 64 (sign_extend' 12 imm_entry)))]> m0) with R1.
    iEval (rewrite stack_own_slots; cbn [seq]) in "Hframe".
    iDestruct "Hframe" as "(S1 & S2 & S3 & S4 & _)".
    iDestruct "S1" as (vr24) "Hr24". iDestruct "S2" as (vr16) "Hr16".
    iDestruct "S3" as (vr8)  "Hr8".  iDestruct "S4" as (vg4)  "Hg4".
    assert (Hb1 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb2 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb3 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    assert (Hb4 : add_vec (R1 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 0 : mword 6) ('b"000"))) = pa_stk sp0 4).
    { rewrite Hcsp1. unfold sp', sp0, pa_stk, add_vec_int, imm_entry. rewrite add_vec_off2.
      f_equal; try (apply bv_eq; vm_compute; reflexivity). }
    iEval (rewrite -Hb1) in "Hr24". iEval (rewrite -Hb2) in "Hr16".
    iEval (rewrite -Hb3) in "Hr8".
    (* ---- 0x02: c.sdsp ra,24(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x02)) (mword_of_int 3 : mword 6) ra_idx R1 (n - 4)%nat vr24
              with "Hcg Hpc Hi02 Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp04 : add_vec_int (mword_of_int (PC + 0x02) : mword 64) 2 = mword_of_int (PC + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    (* ---- 0x04: c.sdsp s0,16(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x04)) (mword_of_int 2 : mword 6) s0_idx R1 (n - 4)%nat vr16
              with "Hcg Hpc Hi04 Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp06 : add_vec_int (mword_of_int (PC + 0x04) : mword 64) 2 = mword_of_int (PC + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    (* ---- 0x06: c.sdsp s1,8(sp) ---- *)
    iApply (wp_csdsp_s_sconf γ Φ (mword_of_int (PC + 0x06)) (mword_of_int 1 : mword 6) s1_idx R1 (n - 4)%nat vr8
              with "Hcg Hpc Hi06 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp08 : add_vec_int (mword_of_int (PC + 0x06) : mword 64) 2 = mword_of_int (PC + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    (* ---- 0x08: c.addi4spn s0,sp,32 ---- *)
    iApply (wp_caddi4spn_s_sconf γ Φ (mword_of_int (PC + 0x08)) (Cregidx (mword_of_int 0)) nzimm_s0 s0_idx R1 (n - 4)%nat
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi08 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0a : add_vec_int (mword_of_int (PC + 0x08) : mword 64) 2 = mword_of_int (PC + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg (add_vec (R1 !!! Regidx csp_rs1) (sign_extend' 64 (caddi4spn_imm nzimm_s0)))]> R1) with R2.
    (* ---- 0x0a: c.mv s1,a0 ---- *)
    iApply (wp_cmv_s_sconf γ Φ (mword_of_int (PC + 0x0a)) s1_idx a0_idx R2 (n - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi0a [-]").
    iIntros "Hcg Hpc".
    assert (Hpp0c : add_vec_int (mword_of_int (PC + 0x0a) : mword 64) 2 = mword_of_int (PC + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    change (<[Regidx s1_idx := regval_into_reg (add_vec zero_reg (R2 !!! Regidx a0_idx))]> R2) with R3.
    assert (HR3sp : R3 !!! Regidx csp_rs1 = sp').
    { unfold R3, R2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hcsp1. }
    assert (HR3tp : R3 !!! Regidx (mword_of_int 4 : mword 5) = m0 !!! Regidx tp_idx).
    { unfold R3, R2, R1. repeat (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity. }
    (* ---- 0x0c: jal ra,cpuid ---- *)
    iApply (Cpuid.wp_call_cpuid_sconf_cs γ Φ (mword_of_int (PC + 0x0c))
              (mword_of_int 2081752 : mword 21) R3 (n - 4)%nat
              ltac:(apply bv_eq; vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity)
              ltac:(lia)
              with "Hcg Htext Hpc Hi0c [-]").
    iIntros (mo) "Hcg Hpc %Hmo".
    destruct Hmo as [Hmo_cs Hmo_a0].
    iEval (rewrite upd_eq) in "Hpc".
    assert (Hpc10 : ret_pc (add_vec_int (mword_of_int (PC + 0x0c) : mword 64) 4)
                       = (mword_of_int (PC + 0x10) : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpc10) in "Hpc".
    assert (Hmosp : mo !!! Regidx csp_rs1 = sp')
      by (rewrite (proj1 Hmo_cs); exact HR3sp).
    assert (Hmoa0 : mo !!! Regidx a0_idx = m0 !!! Regidx tp_idx).
    { unfold a0_idx. rewrite Hmo_a0 HR3tp. exact (sext32_id_hart _ Hhart). }
    (* ---- the post-call register-map chain ---- *)
    set (N2 := <[Regidx a5_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 13)]> mo).
    set (N3 := <[Regidx a4_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N2).
    set (N4 := <[Regidx a5_idx := regval_into_reg (add_vec (N3 !!! Regidx a5_idx) (N3 !!! Regidx a4_idx))]> N3).
    set (N5 := <[Regidx ra_idx := regval_into_reg ra0]> N4).
    set (N6 := <[Regidx s0_idx := regval_into_reg s00]> N5).
    set (N7 := <[Regidx s1_idx := regval_into_reg s10]> N6).
    set (N8 := <[Regidx csp_rs1 := regval_into_reg (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> N7).
    (* ---- 0x10: slliw a5,a0,13 ---- *)
    iApply (wp_slliw_s_sconf γ Φ (mword_of_int (PC + 0x10)) a5_idx a0_idx
              (mword_of_int 13 : mword 5) (ph_shl (m0 !!! Regidx tp_idx) 13) mo (n - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(rewrite Hmoa0; reflexivity)
              with "Hcg Hpc Hi10 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp14 : add_vec_int (mword_of_int (PC + 0x10) : mword 64) 4 = mword_of_int (PC + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (ph_shl (m0 !!! Regidx tp_idx) 13)]> mo) with N2.
    (* ---- 0x14: lui a4,0xc201 ---- *)
    iApply (wp_lui_s_sconf γ Φ (mword_of_int (PC + 0x14)) a4_idx
              (mword_of_int 0xc201 : mword 20) (mword_of_int 0x0c201000 : mword 64) N2 (n - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              ltac:(apply bv_eq; vm_compute; reflexivity)
              with "Hcg Hpc Hi14 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp18 : add_vec_int (mword_of_int (PC + 0x14) : mword 64) 4 = mword_of_int (PC + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    change (<[Regidx a4_idx := regval_into_reg (mword_of_int 0x0c201000 : mword 64)]> N2) with N3.
    (* ---- 0x18: c.add a5,a5,a4 ---- *)
    iApply (wp_cadd_s_sconf γ Φ (mword_of_int (PC + 0x18)) a5_idx a4_idx N3 (n - 4)%nat
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi18 [-]").
    iIntros "Hcg Hpc".
    assert (Hpp1a : add_vec_int (mword_of_int (PC + 0x18) : mword 64) 2 = mword_of_int (PC + 0x1a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1a) in "Hpc".
    change (<[Regidx a5_idx := regval_into_reg (add_vec (N3 !!! Regidx a5_idx) (N3 !!! Regidx a4_idx))]> N3) with N4.
    assert (HN3a5 : N3 !!! Regidx a5_idx = ph_shl (m0 !!! Regidx tp_idx) 13).
    { unfold N3. rewrite upd_ne; [| vm_compute; discriminate]. unfold N2. apply upd_eq. }
    assert (HN3a4 : N3 !!! Regidx a4_idx = (mword_of_int 0x0c201000 : mword 64))
      by (unfold N3; apply upd_eq).
    assert (HN4a5 : N4 !!! Regidx a5_idx = ph_sthb (m0 !!! Regidx tp_idx)).
    { unfold N4. rewrite upd_eq. unfold regval_into_reg.
      rewrite HN3a5 HN3a4. unfold ph_sthb. apply ph_add_comm. }
    (* ---- 0x1a: c.sw s1,4(a5) -- PLIC_SCLAIM(hart) = irq ---- *)
    iApply (wp_sw_plic_dev_s_sconf γ γd γv Φ (mword_of_int (PC + 0x1a)) true s1_idx a5_idx
              (mword_of_int 4 : mword 12) N4 (n - 4)%nat
              ltac:(rewrite HN4a5; exact (ph_geom_range _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_align _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_canon _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; exact (ph_geom_vpn   _ (ph_sclaim_geom _ Hhart)))
              ltac:(rewrite HN4a5; intros pq Hpq; eexists; split;
                    [ exact (ph_sclaim_write _ pq _ Hhart)
                    | apply plic_ok_complete; exact Hpq ])
              with "Hcg Hpc Hi1a Hdinv").
    iIntros "Hcg Hpc".
    assert (Hpp1c : add_vec_int (mword_of_int (PC + 0x1a) : mword 64) 2 = mword_of_int (PC + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    (* ---- the epilogue ---- *)
    assert (HN4sp : N4 !!! Regidx csp_rs1 = sp').
    { unfold N4, N3, N2. repeat (rewrite upd_ne; [| vm_compute; discriminate]). exact Hmosp. }
    assert (Hb1' : add_vec (N4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 3 : mword 6) ('b"000"))) = pa_stk sp0 1).
    { rewrite HN4sp. rewrite -Hcsp1. exact Hb1. }
    assert (Hb2' : add_vec (N4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 2 : mword 6) ('b"000"))) = pa_stk sp0 2).
    { rewrite HN4sp. rewrite -Hcsp1. exact Hb2. }
    assert (Hb3' : add_vec (N4 !!! Regidx csp_rs1) (zero_extend' 64 (concat_vec (mword_of_int 1 : mword 6) ('b"000"))) = pa_stk sp0 3).
    { rewrite HN4sp. rewrite -Hcsp1. exact Hb3. }
    assert (Hra0v : R1 !!! Regidx ra_idx = ra0)
      by (unfold R1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs00v : R1 !!! Regidx s0_idx = s00)
      by (unfold R1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    assert (Hs10v : R1 !!! Regidx s1_idx = s10)
      by (unfold R1; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite Hb1 -Hb1' Hra0v) in "Hr24".
    iEval (rewrite Hb2 -Hb2' Hs00v) in "Hr16".
    iEval (rewrite Hb3 -Hb3' Hs10v) in "Hr8".
    (* ---- 0x1c: c.ldsp ra,24(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x1c)) (mword_of_int 3 : mword 6) ra_idx N4 (n - 4)%nat ra0
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1c Hr24 [-]").
    iIntros "Hcg Hpc Hr24".
    assert (Hpp1e : add_vec_int (mword_of_int (PC + 0x1c) : mword 64) 2 = mword_of_int (PC + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    change (<[Regidx ra_idx := regval_into_reg ra0]> N4) with N5.
    assert (HN5sp : N5 !!! Regidx csp_rs1 = N4 !!! Regidx csp_rs1)
      by (unfold N5; rewrite upd_ne; [reflexivity | vm_compute; discriminate]).
    iEval (rewrite -HN5sp) in "Hr16".
    (* ---- 0x1e: c.ldsp s0,16(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x1e)) (mword_of_int 2 : mword 6) s0_idx N5 (n - 4)%nat s00
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi1e Hr16 [-]").
    iIntros "Hcg Hpc Hr16".
    assert (Hpp20 : add_vec_int (mword_of_int (PC + 0x1e) : mword 64) 2 = mword_of_int (PC + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    change (<[Regidx s0_idx := regval_into_reg s00]> N5) with N6.
    assert (HN6sp : N6 !!! Regidx csp_rs1 = N4 !!! Regidx csp_rs1).
    { unfold N6, N5. repeat (rewrite upd_ne; [| vm_compute; discriminate]). reflexivity. }
    iEval (rewrite -HN6sp) in "Hr8".
    (* ---- 0x20: c.ldsp s1,8(sp) ---- *)
    iApply (wp_cldsp_s_sconf γ Φ (mword_of_int (PC + 0x20)) (mword_of_int 1 : mword 6) s1_idx N6 (n - 4)%nat s10
              ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi20 Hr8 [-]").
    iIntros "Hcg Hpc Hr8".
    assert (Hpp22 : add_vec_int (mword_of_int (PC + 0x20) : mword 64) 2 = mword_of_int (PC + 0x22)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp22) in "Hpc".
    change (<[Regidx s1_idx := regval_into_reg s10]> N6) with N7.
    (* ---- 0x22: c.addi16sp sp,32 -- the frame pop ---- *)
    assert (HN7sp : N7 !!! Regidx csp_rs1 = sp').
    { unfold N7. rewrite upd_ne; [| vm_compute; discriminate]. rewrite HN6sp. exact HN4sp. }
    assert (Hwv : add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))) = sp0).
    { rewrite HN7sp. unfold sp', imm_entry, sp0. apply frame_cancel_32. }
    assert (Hpop : N7 !!! Regidx csp_rs1
                   = pa_stk (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6)))) 4).
    { rewrite Hwv HN7sp. unfold sp', imm_entry, sp0. exact Hpush. }
    iAssert (stack_own sp0 4) with "[Hr24 Hr16 Hr8 Hg4]" as "Hframe4".
    { rewrite stack_own_slots. cbn [seq].
      iSplitL "Hr24"; [iEval (rewrite -Hb1 Hcsp1 -HN4sp); iExists _; iExact "Hr24"|].
      iSplitL "Hr16"; [iEval (rewrite -Hb2 Hcsp1 -HN4sp -HN5sp); iExists _; iExact "Hr16"|].
      iSplitL "Hr8";  [iEval (rewrite -Hb3 Hcsp1 -HN4sp -HN6sp); iExists _; iExact "Hr8"|].
      iSplitL "Hg4";  [iExists _; iExact "Hg4"|].
      done. }
    iEval (rewrite -Hwv) in "Hframe4".
    iApply (wp_caddi16sp_pop_s_sconf γ Φ (mword_of_int (PC + 0x22)) (mword_of_int 2 : mword 6) N7
              (n - 4)%nat 4 Hpop
              with "Hcg Hpc Hi22 Hframe4 [-]").
    iIntros "Hcg Hpc".
    assert (Hnk : ((n - 4) + 4)%nat = n) by lia.
    iEval (rewrite Hnk) in "Hcg".
    assert (Hpp24 : add_vec_int (mword_of_int (PC + 0x22) : mword 64) 2 = mword_of_int (PC + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    change (<[Regidx csp_rs1 := regval_into_reg (add_vec (N7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 2 : mword 6))))]> N7) with N8.
    (* ---- 0x24: c.ret ---- *)
    assert (HN8ra : N8 !!! Regidx ra_idx = ra0).
    { unfold N8, N7, N6. repeat (rewrite upd_ne; [| vm_compute; discriminate]).
      unfold N5. rewrite upd_eq. reflexivity. }
    iApply (wp_cret_s_sconf γ Φ (mword_of_int (PC + 0x24)) ra_idx N8 n
              ltac:(vm_compute; discriminate)
              with "Hcg Hpc Hi24 [-]").
    iIntros "Hcg Hpc".
    assert (Hra_final : ret_pc (N8 !!! Regidx ra_idx) = ret_tgt)
      by (rewrite HN8ra; reflexivity).
    iEval (rewrite Hra_final) in "Hpc".
    iApply ("Hcont" $! N8 with "Hcg Hpc [%]").
    split.
    - (* sp, s0 and s1 are saved-then-restored ACROSS the call, so the fact does
         not factor through the callee's [callee_saved]; each conjunct on its own. *)
      unfold callee_saved.
      split.
      { unfold N8. rewrite upd_eq. unfold regval_into_reg. exact Hwv. }
      split; [ cs_through Hmo_cs mo | ].
      split.
      { unfold N8, N7, N6, s0_idx, s00.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq. unfold regval_into_reg. reflexivity. }
      split.
      { unfold N8, N7, s1_idx, s10.
        rewrite upd_ne; [| vm_compute; discriminate].
        rewrite upd_eq. unfold regval_into_reg. reflexivity. }
      repeat split; cs_through Hmo_cs mo.
    - exact HN8ra.
  Qed.
   ----------------------------------------------------------------------- *)

End ProofPlicComplete.

End PlicCompleteProof.

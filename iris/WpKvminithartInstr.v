(* WpKvminithartInstr.v -- decode catalog for xv6's kvminithart()
   (kernel/vm.c).  Per-instruction decode facts + [instr] constructors,
   consumed by the wp_kvminithart proof; same architecture as
   WpKvmmakeInstr.v.

   kvminithart body = KernelInstrs.v bytes at KernelSyms.kvminithart
   (0x80000f30 .. 0x80000f5c, 17 instrs): the 2-slot frame (addi sp,-16;
   ra/s0 saves; addi s0,sp,16), a first sfence.vma zero,zero, the
   auipc/ld of kernel_pagetable (@ 0x8000a238) into a5, the SATP value
   assembly (srli a5,12; li a4,-1; slli a4,0x3f; or a5,a5,a4), the
   csrw satp,a5, the second sfence.vma, and the 2-slot frame teardown +
   ret.  Immediates/ASTs are the exact vm_compute-on-decode outputs
   against the reference config state (dstateM/dstateS). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode.
Import Defs.

Section KvminithartInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation KVI off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.kvminithart + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* All compressed forms appearing here (C.ADDI, C.SDSP, C.ADDI4SPN,
     C.SRLI, C.LI, C.SLLI, C.OR, C.LDSP, C.JR) have their ExecuteAs
     redirects in WpMmodeLeafBase -- no Local copies are needed. *)

  Lemma kvidec_08 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x12000073 : mword 32)) s
    = Some (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvidec_0c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00009797 : mword 32)) s
    = Some (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvidec_10 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x2fc7b783 : mword 32)) s
    = Some (LOAD (mword_of_int 764 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 8), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvidec_16 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x577d : mword 16)) s
    = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvidec_18 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x177e : mword 16)) s
    = Some (C_SLLI (mword_of_int 63, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kvidec_1c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x18079073 : mword 32)) s
    = Some (CSRReg (mword_of_int 384 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 0), CSRRW), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kvidec_20 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x12000073 : mword 32)) s
    = Some (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  (* ---- kvminithart instr lemmas ---- *)
  Lemma kvi_00 : KVI 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (* addi sp,sp,-16 *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x00)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
  Lemma kvi_02 : KVI 0x02 true (STORE (csdsp_imm 1, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x02) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
  Lemma kvi_04 : KVI 0x04 true (STORE (csdsp_imm 0, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x04)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x04) : mword 64) (STORE (csdsp_imm 0, Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
  Lemma kvi_06 : KVI 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,16 *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
  Lemma kvi_08 : KVI 0x08 false (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0))).  (* sfence.vma zero,zero *)
  Proof. mk_base (KernelSyms.kvminithart + 0x08)%Z (mword_of_int 0x12000073 : mword 32) (mword_of_int (KernelSyms.kvminithart + 0x08) : mword 64) (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0))) kvidec_08. Qed.
  Lemma kvi_0c : KVI 0x0c false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)).  (* auipc a5,0x9 *)
  Proof. mk_base (KernelSyms.kvminithart + 0x0c)%Z (mword_of_int 0x00009797 : mword 32) (mword_of_int (KernelSyms.kvminithart + 0x0c) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)) kvidec_0c. Qed.
  Lemma kvi_10 : KVI 0x10 false (LOAD (mword_of_int 764 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 8)).  (* ld a5,764(a5) # 8000a238 <kernel_pagetable> *)
  Proof. mk_base (KernelSyms.kvminithart + 0x10)%Z (mword_of_int 0x2fc7b783 : mword 32) (mword_of_int (KernelSyms.kvminithart + 0x10) : mword 64) (LOAD (mword_of_int 764 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 8)) kvidec_10. Qed.
  Lemma kvi_14 : KVI 0x14 true (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).  (* srli a5,a5,0xc *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x14)%Z (mword_of_int 0x83b1 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x14) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83b1 exec_execute_C_SRLI. Qed.
  Lemma kvi_16 : KVI 0x16 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,-1 *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x16)%Z (mword_of_int 0x577d : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kvidec_16 exec_execute_C_LI. Qed.
  Lemma kvi_18 : KVI 0x18 true (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)).  (* slli a4,a4,0x3f *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x18)%Z (mword_of_int 0x177e : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x18) : mword 64) (SHIFTIOP (mword_of_int 63 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLLI)) kvidec_18 exec_execute_C_SLLI. Qed.
  Lemma kvi_1a : KVI 0x1a true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), OR)).  (* or a5,a5,a4 *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x1a)%Z (mword_of_int 0x8fd9 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x1a) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), OR)) cdec_8fd9 exec_execute_C_OR. Qed.
  Lemma kvi_1c : KVI 0x1c false (CSRReg (mword_of_int 384 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 0), CSRRW)).  (* csrw satp,a5 *)
  Proof. mk_base (KernelSyms.kvminithart + 0x1c)%Z (mword_of_int 0x18079073 : mword 32) (mword_of_int (KernelSyms.kvminithart + 0x1c) : mword 64) (CSRReg (mword_of_int 384 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 0), CSRRW)) kvidec_1c. Qed.
  Lemma kvi_20 : KVI 0x20 false (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0))).  (* sfence.vma zero,zero *)
  Proof. mk_base (KernelSyms.kvminithart + 0x20)%Z (mword_of_int 0x12000073 : mword 32) (mword_of_int (KernelSyms.kvminithart + 0x20) : mword 64) (SFENCE_VMA (Regidx (mword_of_int 0), Regidx (mword_of_int 0))) kvidec_20. Qed.
  Lemma kvi_24 : KVI 0x24 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x24)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x24) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
  Lemma kvi_26 : KVI 0x26 true (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x26)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x26) : mword 64) (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
  Lemma kvi_28 : KVI 0x28 true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (* addi sp,sp,16 *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x28)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
  Lemma kvi_2a : KVI 0x2a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.kvminithart + 0x2a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.kvminithart + 0x2a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End KvminithartInstrs.

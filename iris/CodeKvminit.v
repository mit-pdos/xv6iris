(* CodeKvminit.v -- the machine code of xv6's kvminit() (kernel/vm.c): the
   per-instruction decode facts and [instr] constructors at KernelSyms.kvminit
   (0x800011bc .. 0x800011d8, 11 instrs) -- the 2-slot frame, the kvmmake jal,
   and the sd into kernel_pagetable @ 0x8000a238 via auipc a5,0x9 /
   sd a0,112(a5).  JAL residues = (target - pc) mod 2^21; immediates/ASTs are
   the exact vm_compute-on-decode outputs. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.

Section CodeKvminit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation KIN off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.kvminit + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  Lemma kidec_08 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf4bff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096970 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kidec_10 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x06a7b823 : mword 32)) s
    = Some (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 8), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  (* ---- kvminit instr lemmas ---- *)
  Lemma kii_00 : KIN 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (*  *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x00)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.
  Lemma kii_02 : KIN 0x02 true (STORE (csdsp_imm 1, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x02) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.
  Lemma kii_04 : KIN 0x04 true (STORE (csdsp_imm 0, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x04)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x04) : mword 64) (STORE (csdsp_imm 0, Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.
  Lemma kii_06 : KIN 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,16 *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.
  Lemma kii_08 : KIN 0x08 false (JAL (mword_of_int 2096970 : mword 21, Regidx (mword_of_int 1))).  (* jal 8000110e <kvmmake> *)
  Proof. mk_base (KernelSyms.kvminit + 0x08)%Z (mword_of_int 0xf4bff0ef : mword 32) (mword_of_int (KernelSyms.kvminit + 0x08) : mword 64) (JAL (mword_of_int 2096970 : mword 21, Regidx (mword_of_int 1))) kidec_08. Qed.
  Lemma kii_0c : KIN 0x0c false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)).  (* auipc a5,0x9 *)
  Proof. mk_base (KernelSyms.kvminit + 0x0c)%Z (mword_of_int 0x00009797 : mword 32) (mword_of_int (KernelSyms.kvminit + 0x0c) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_00009797. Qed.
  Lemma kii_10 : KIN 0x10 false (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 8)).  (* sd a0,112(a5) # 8000a238 <kernel_pagetable> *)
  Proof. mk_base (KernelSyms.kvminit + 0x10)%Z (mword_of_int 0x06a7b823 : mword 32) (mword_of_int (KernelSyms.kvminit + 0x10) : mword 64) (STORE (mword_of_int 112 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), 8)) kidec_10. Qed.
  Lemma kii_14 : KIN 0x14 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x14)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x14) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.
  Lemma kii_16 : KIN 0x16 true (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,0(sp) *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x16)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x16) : mword 64) (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.
  Lemma kii_18 : KIN 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (* addi sp,sp,16 *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x18)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.
  Lemma kii_1a : KIN 0x1a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.kvminit + 0x1a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.kvminit + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeKvminit.

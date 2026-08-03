(* CodeKvmmake.v -- the machine code of xv6's kvmmake() (kernel/vm.c): the
   per-instruction decode facts and [instr] constructors at KernelSyms.kvmmake
   (0x8000110e .. 0x800011bc, 64 instrs) -- the 4-slot frame (addi sp,-32;
   ra/s0/s1 saves), the root kalloc jal, the memset jal, the six
   {lui/auipc/addi arg setup + kvmmap jal} region groups, and the
   proc_mapstacks jal.  JAL residues = (target - pc) mod 2^21; immediates/ASTs
   are the exact vm_compute-on-decode outputs.  kvminit's code is in
   CodeKvminit.v. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
Import Defs.

Section CodeKvmmake.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation KMK off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.kvmmake + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  Lemma kmkdec_0a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xa17ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095638 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_14 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xba7ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096038 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_18 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4719 : mword 16)) s
    = Some (C_LI (mword_of_int 6, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_1a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6685 : mword 16)) s
    = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 13)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_1c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x10000637 : mword 32)) s
    = Some (UTYPE (mword_of_int 65536 : mword 20, Regidx (mword_of_int 12), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_20 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x85b2 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_24 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfb5ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2097076 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_2c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x10001637 : mword 32)) s
    = Some (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 12), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_34 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfa5ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2097060 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_3a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x040006b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 13), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_3e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x0c000637 : mword 32)) s
    = Some (UTYPE (mword_of_int 49152 : mword 20, Regidx (mword_of_int 12), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_46 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf93ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2097042 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_4a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4729 : mword 16)) s
    = Some (C_LI (mword_of_int 10, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_4c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x80006697 : mword 32)) s
    = Some (UTYPE (mword_of_int 524294 : mword 20, Regidx (mword_of_int 13), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_50 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xea668693 : mword 32)) s
    = Some (ITYPE (mword_of_int 3750 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_54 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4605 : mword 16)) s
    = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x067e : mword 16)) s
    = Some (C_SLLI (mword_of_int 31, Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_5c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf7dff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2097020 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_62 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00006697 : mword 32)) s
    = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 13), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_66 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xe9068693 : mword 32)) s
    = Some (ITYPE (mword_of_int 3728 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_6e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x40d786b3 : mword 32)) s
    = Some (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 15), Regidx (mword_of_int 13), SUB), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_72 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00006617 : mword 32)) s
    = Some (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 12), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_76 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xe8060613 : mword 32)) s
    = Some (ITYPE (mword_of_int 3712 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_7e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf5bff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096986 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_86 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00005617 : mword 32)) s
    = Some (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 12), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_8a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xe6c60613 : mword 32)) s
    = Some (ITYPE (mword_of_int 3692 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_8e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x040005b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_92 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x15fd : mword 16)) s
    = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_94 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x05b2 : mword 16)) s
    = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma kmkdec_98 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xf41ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096960 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma kmkdec_9e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x5ca000ef : mword 32)) s
    = Some (JAL (mword_of_int 1482 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  (* ---- kvmmake instr lemmas ---- *)
  Lemma kmki_00 : KMK 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (*  *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
  Lemma kmki_02 : KMK 0x02 true (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x02) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
  Lemma kmki_04 : KMK 0x04 true (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x04) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
  Lemma kmki_06 : KMK 0x06 true (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)).  (* sd s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x06) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.
  Lemma kmki_08 : KMK 0x08 true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,32 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x08)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
  Lemma kmki_0a : KMK 0x0a false (JAL (mword_of_int 2095638 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000b2e <kalloc> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x0a)%Z (mword_of_int 0xa17ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x0a) : mword 64) (JAL (mword_of_int 2095638 : mword 21, Regidx (mword_of_int 1))) kmkdec_0a. Qed.
  Lemma kmki_0e : KMK 0x0e true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).  (* mv s1,a0 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x0e)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
  Lemma kmki_10 : KMK 0x10 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).  (* lui a2,0x1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x10)%Z (mword_of_int 0x6605 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x10) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.
  Lemma kmki_12 : KMK 0x12 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).  (* li a1,0 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x12)%Z (mword_of_int 0x4581 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x12) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.
  Lemma kmki_14 : KMK 0x14 false (JAL (mword_of_int 2096038 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000cc8 <memset> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x14)%Z (mword_of_int 0xba7ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x14) : mword 64) (JAL (mword_of_int 2096038 : mword 21, Regidx (mword_of_int 1))) kmkdec_14. Qed.
  Lemma kmki_18 : KMK 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,6 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x18)%Z (mword_of_int 0x4719 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_18 exec_execute_C_LI. Qed.
  Lemma kmki_1a : KMK 0x1a true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)).  (* lui a3,0x1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x1a)%Z (mword_of_int 0x6685 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x1a) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)) kmkdec_1a exec_execute_C_LUI. Qed.
  Lemma kmki_1c : KMK 0x1c false (UTYPE (mword_of_int 65536 : mword 20, Regidx (mword_of_int 12), LUI)).  (* lui a2,0x10000 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x1c)%Z (mword_of_int 0x10000637 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x1c) : mword 64) (UTYPE (mword_of_int 65536 : mword 20, Regidx (mword_of_int 12), LUI)) kmkdec_1c. Qed.
  Lemma kmki_20 : KMK 0x20 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).  (* mv a1,a2 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x20)%Z (mword_of_int 0x85b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) kmkdec_20 exec_execute_C_MV. Qed.
  Lemma kmki_22 : KMK 0x22 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x22)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_24 : KMK 0x24 false (JAL (mword_of_int 2097076 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x24)%Z (mword_of_int 0xfb5ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x24) : mword 64) (JAL (mword_of_int 2097076 : mword 21, Regidx (mword_of_int 1))) kmkdec_24. Qed.
  Lemma kmki_28 : KMK 0x28 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,6 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x28)%Z (mword_of_int 0x4719 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_18 exec_execute_C_LI. Qed.
  Lemma kmki_2a : KMK 0x2a true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)).  (* lui a3,0x1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x2a)%Z (mword_of_int 0x6685 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x2a) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)) kmkdec_1a exec_execute_C_LUI. Qed.
  Lemma kmki_2c : KMK 0x2c false (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 12), LUI)).  (* lui a2,0x10001 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x2c)%Z (mword_of_int 0x10001637 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x2c) : mword 64) (UTYPE (mword_of_int 65537 : mword 20, Regidx (mword_of_int 12), LUI)) kmkdec_2c. Qed.
  Lemma kmki_30 : KMK 0x30 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).  (* mv a1,a2 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x30)%Z (mword_of_int 0x85b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) kmkdec_20 exec_execute_C_MV. Qed.
  Lemma kmki_32 : KMK 0x32 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x32)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_34 : KMK 0x34 false (JAL (mword_of_int 2097060 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x34)%Z (mword_of_int 0xfa5ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x34) : mword 64) (JAL (mword_of_int 2097060 : mword 21, Regidx (mword_of_int 1))) kmkdec_34. Qed.
  Lemma kmki_38 : KMK 0x38 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,6 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x38)%Z (mword_of_int 0x4719 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x38) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_18 exec_execute_C_LI. Qed.
  Lemma kmki_3a : KMK 0x3a false (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 13), LUI)).  (* lui a3,0x4000 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x3a)%Z (mword_of_int 0x040006b7 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x3a) : mword 64) (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 13), LUI)) kmkdec_3a. Qed.
  Lemma kmki_3e : KMK 0x3e false (UTYPE (mword_of_int 49152 : mword 20, Regidx (mword_of_int 12), LUI)).  (* lui a2,0xc000 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x3e)%Z (mword_of_int 0x0c000637 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x3e) : mword 64) (UTYPE (mword_of_int 49152 : mword 20, Regidx (mword_of_int 12), LUI)) kmkdec_3e. Qed.
  Lemma kmki_42 : KMK 0x42 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).  (* mv a1,a2 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x42)%Z (mword_of_int 0x85b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) kmkdec_20 exec_execute_C_MV. Qed.
  Lemma kmki_44 : KMK 0x44 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x44)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_46 : KMK 0x46 false (JAL (mword_of_int 2097042 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x46)%Z (mword_of_int 0xf93ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x46) : mword 64) (JAL (mword_of_int 2097042 : mword 21, Regidx (mword_of_int 1))) kmkdec_46. Qed.
  Lemma kmki_4a : KMK 0x4a true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,10 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x4a)%Z (mword_of_int 0x4729 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x4a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_4a exec_execute_C_LI. Qed.
  Lemma kmki_4c : KMK 0x4c false (UTYPE (mword_of_int 524294 : mword 20, Regidx (mword_of_int 13), AUIPC)).  (* auipc a3,0x80006 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x4c)%Z (mword_of_int 0x80006697 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x4c) : mword 64) (UTYPE (mword_of_int 524294 : mword 20, Regidx (mword_of_int 13), AUIPC)) kmkdec_4c. Qed.
  Lemma kmki_50 : KMK 0x50 false (ITYPE (mword_of_int 3750 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).  (* addi a3,a3,-346 # 7000 <_entry-0x7fff9000> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x50)%Z (mword_of_int 0xea668693 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x50) : mword 64) (ITYPE (mword_of_int 3750 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) kmkdec_50. Qed.
  Lemma kmki_54 : KMK 0x54 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).  (* li a2,1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x54)%Z (mword_of_int 0x4605 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x54) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) kmkdec_54 exec_execute_C_LI. Qed.
  Lemma kmki_56 : KMK 0x56 true (SHIFTIOP (mword_of_int 31 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).  (* slli a2,a2,0x1f *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x56)%Z (mword_of_int 0x067e : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x56) : mword 64) (SHIFTIOP (mword_of_int 31 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) kmkdec_56 exec_execute_C_SLLI. Qed.
  Lemma kmki_58 : KMK 0x58 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).  (* mv a1,a2 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x58)%Z (mword_of_int 0x85b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) kmkdec_20 exec_execute_C_MV. Qed.
  Lemma kmki_5a : KMK 0x5a true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x5a)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_5c : KMK 0x5c false (JAL (mword_of_int 2097020 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x5c)%Z (mword_of_int 0xf7dff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x5c) : mword 64) (JAL (mword_of_int 2097020 : mword 21, Regidx (mword_of_int 1))) kmkdec_5c. Qed.
  Lemma kmki_60 : KMK 0x60 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,6 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x60)%Z (mword_of_int 0x4719 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x60) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_18 exec_execute_C_LI. Qed.
  Lemma kmki_62 : KMK 0x62 false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 13), AUIPC)).  (* auipc a3,0x6 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x62)%Z (mword_of_int 0x00006697 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x62) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 13), AUIPC)) kmkdec_62. Qed.
  Lemma kmki_66 : KMK 0x66 false (ITYPE (mword_of_int 3728 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).  (* addi a3,a3,-368 # 80007000 <etext> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x66)%Z (mword_of_int 0xe9068693 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x66) : mword 64) (ITYPE (mword_of_int 3728 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) kmkdec_66. Qed.
  Lemma kmki_6a : KMK 0x6a true (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).  (* li a5,17 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x6a)%Z (mword_of_int 0x47c5 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x6a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_47c5 exec_execute_C_LI. Qed.
  Lemma kmki_6c : KMK 0x6c true (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).  (* slli a5,a5,0x1b *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x6c)%Z (mword_of_int 0x07ee : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x6c) : mword 64) (SHIFTIOP (mword_of_int 27 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_07ee exec_execute_C_SLLI. Qed.
  Lemma kmki_6e : KMK 0x6e false (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 15), Regidx (mword_of_int 13), SUB)).  (* sub a3,a5,a3 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x6e)%Z (mword_of_int 0x40d786b3 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x6e) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 15), Regidx (mword_of_int 13), SUB)) kmkdec_6e. Qed.
  Lemma kmki_72 : KMK 0x72 false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 12), AUIPC)).  (* auipc a2,0x6 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x72)%Z (mword_of_int 0x00006617 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x72) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 12), AUIPC)) kmkdec_72. Qed.
  Lemma kmki_76 : KMK 0x76 false (ITYPE (mword_of_int 3712 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).  (* addi a2,a2,-384 # 80007000 <etext> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x76)%Z (mword_of_int 0xe8060613 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x76) : mword 64) (ITYPE (mword_of_int 3712 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) kmkdec_76. Qed.
  Lemma kmki_7a : KMK 0x7a true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)).  (* mv a1,a2 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x7a)%Z (mword_of_int 0x85b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 11), ADD)) kmkdec_20 exec_execute_C_MV. Qed.
  Lemma kmki_7c : KMK 0x7c true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x7c)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x7c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_7e : KMK 0x7e false (JAL (mword_of_int 2096986 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x7e)%Z (mword_of_int 0xf5bff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x7e) : mword 64) (JAL (mword_of_int 2096986 : mword 21, Regidx (mword_of_int 1))) kmkdec_7e. Qed.
  Lemma kmki_82 : KMK 0x82 true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,10 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x82)%Z (mword_of_int 0x4729 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x82) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) kmkdec_4a exec_execute_C_LI. Qed.
  Lemma kmki_84 : KMK 0x84 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)).  (* lui a3,0x1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x84)%Z (mword_of_int 0x6685 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x84) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 13), LUI)) kmkdec_1a exec_execute_C_LUI. Qed.
  Lemma kmki_86 : KMK 0x86 false (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 12), AUIPC)).  (* auipc a2,0x5 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x86)%Z (mword_of_int 0x00005617 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x86) : mword 64) (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 12), AUIPC)) kmkdec_86. Qed.
  Lemma kmki_8a : KMK 0x8a false (ITYPE (mword_of_int 3692 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).  (* addi a2,a2,-404 # 80006000 <_trampoline> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x8a)%Z (mword_of_int 0xe6c60613 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x8a) : mword 64) (ITYPE (mword_of_int 3692 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) kmkdec_8a. Qed.
  Lemma kmki_8e : KMK 0x8e false (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)).  (* lui a1,0x4000 *)
  Proof. mk_base (KernelSyms.kvmmake + 0x8e)%Z (mword_of_int 0x040005b7 : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x8e) : mword 64) (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)) kmkdec_8e. Qed.
  Lemma kmki_92 : KMK 0x92 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).  (* addi a1,a1,-1 # 3ffffff <_entry-0x7c000001> *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x92)%Z (mword_of_int 0x15fd : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x92) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) kmkdec_92 exec_execute_C_ADDI. Qed.
  Lemma kmki_94 : KMK 0x94 true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* slli a1,a1,0xc *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x94)%Z (mword_of_int 0x05b2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x94) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) kmkdec_94 exec_execute_C_SLLI. Qed.
  Lemma kmki_96 : KMK 0x96 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x96)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x96) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_98 : KMK 0x98 false (JAL (mword_of_int 2096960 : mword 21, Regidx (mword_of_int 1))).  (* jal 800010e6 <kvmmap> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x98)%Z (mword_of_int 0xf41ff0ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x98) : mword 64) (JAL (mword_of_int 2096960 : mword 21, Regidx (mword_of_int 1))) kmkdec_98. Qed.
  Lemma kmki_9c : KMK 0x9c true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0x9c)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0x9c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_9e : KMK 0x9e false (JAL (mword_of_int 1482 : mword 21, Regidx (mword_of_int 1))).  (* jal 80001776 <proc_mapstacks> *)
  Proof. mk_base (KernelSyms.kvmmake + 0x9e)%Z (mword_of_int 0x5ca000ef : mword 32) (mword_of_int (KernelSyms.kvmmake + 0x9e) : mword 64) (JAL (mword_of_int 1482 : mword 21, Regidx (mword_of_int 1))) kmkdec_9e. Qed.
  Lemma kmki_a2 : KMK 0xa2 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xa2)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xa2) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma kmki_a4 : KMK 0xa4 true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xa4)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xa4) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
  Lemma kmki_a6 : KMK 0xa6 true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xa6)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xa6) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
  Lemma kmki_a8 : KMK 0xa8 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)).  (* ld s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xa8)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xa8) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.
  Lemma kmki_aa : KMK 0xaa true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).  (* addi sp,sp,32 *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xaa)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xaa) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
  Lemma kmki_ac : KMK 0xac true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.kvmmake + 0xac)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.kvmmake + 0xac) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeKvmmake.

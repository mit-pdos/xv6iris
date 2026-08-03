(* CodeProcPagetable.v -- decode catalog for xv6's proc_pagetable()
   (kernel/proc.c).  KernelInstrs.v bytes at KernelSyms.proc_pagetable
   (0x80001a0e ..): the 4-slot frame (addi sp,-32; ra/s0/s1/s2 saves), the
   uvmcreate jal + null test, the TRAMPOLINE mappages group (li a4,10;
   auipc/addi a3 -> trampoline; lui a2,0x1; lui/addi/slli a1 -> TRAMPOLINE;
   jal mappages; bltz), the TRAPFRAME group (li a4,6; ld a3,88(s2); ...;
   jal mappages; bltz) and the shared epilogue at +0x4c.

   The catalog covers the SUCCESS path only (+0x00 .. +0x58): the two
   error tails (+0x5a uvmfree, +0x66 uvmunmap/uvmfree) are unreachable
   under the proof's page budget, so no instruction there is ever fetched.

   Same architecture as CodeKvmmake.v; JAL residues = (target-pc) mod 2^21. *)
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
Import Defs.

Section ProcPagetableInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation PPT off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.proc_pagetable + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* ---- decode facts ---- *)
  Lemma pptdec_00 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x1101 : mword 16)) s
    = Some (C_ADDI (mword_of_int 32, Regidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xec06 : mword 16)) s
    = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_04 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe822 : mword 16)) s
    = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe426 : mword 16)) s
    = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_08 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe04a : mword 16)) s
    = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_0a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x1000 : mword 16)) s
    = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 8), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_0c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x892a : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 10)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_0e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfbcff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095036 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_12 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_14 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xcd05 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 28, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_16 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4729 : mword 16)) s
    = Some (C_LI (mword_of_int 10, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_18 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00004697 : mword 32)) s
    = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 13), AUIPC), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_1c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x5da68693 : mword 32)) s
    = Some (ITYPE (mword_of_int 1498 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_20 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6605 : mword 16)) s
    = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_22 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x040005b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x15fd : mword 16)) s
    = Some (C_ADDI (mword_of_int 63, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_28 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x05b2 : mword 16)) s
    = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_2a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xdf8ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2094584 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_2e s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x02054663 : mword 32)) s
    = Some (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_32 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4719 : mword 16)) s
    = Some (C_LI (mword_of_int 6, Regidx (mword_of_int 14)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_34 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x05893683 : mword 32)) s
    = Some (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 13), false, 8), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_3a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x020005b7 : mword 32)) s
    = Some (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 11), LUI), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_40 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x05b6 : mword 16)) s
    = Some (C_SLLI (mword_of_int 13, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_44 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xddeff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2094558 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_48 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x00054f63 : mword 32)) s
    = Some (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma pptdec_4e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x60e2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_50 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6442 : mword 16)) s
    = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_52 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x64a2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_54 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6902 : mword 16)) s
    = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 18)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
    = Some (C_ADDI16SP (mword_of_int 2), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma pptdec_58 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
    = Some (C_JR (Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

  (* ---- instr lemmas ---- *)
  Lemma ppti_00 : PPT 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (* addi sp,sp,-32 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) pptdec_00 exec_execute_C_ADDI. Qed.
  Lemma ppti_02 : PPT 0x02 true (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x02) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)) pptdec_02 exec_execute_C_SDSP. Qed.
  Lemma ppti_04 : PPT 0x04 true (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x04) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)) pptdec_04 exec_execute_C_SDSP. Qed.
  Lemma ppti_06 : PPT 0x06 true (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)).  (* sd s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x06) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)) pptdec_06 exec_execute_C_SDSP. Qed.
  Lemma ppti_08 : PPT 0x08 true (STORE (csdsp_imm 0, Regidx (mword_of_int 18), sp, 8)).  (* sd s2,0(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x08)%Z (mword_of_int 0xe04a : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x08) : mword 64) (STORE (csdsp_imm 0, Regidx (mword_of_int 18), sp, 8)) pptdec_08 exec_execute_C_SDSP. Qed.
  Lemma ppti_0a : PPT 0x0a true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,32 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x0a)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) pptdec_0a exec_execute_C_ADDI4SPN. Qed.
  Lemma ppti_0c : PPT 0x0c true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).  (* mv s2,a0 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x0c)%Z (mword_of_int 0x892a : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) pptdec_0c exec_execute_C_MV. Qed.
  Lemma ppti_0e : PPT 0x0e false (JAL (mword_of_int 2095036 : mword 21, Regidx (mword_of_int 1))).  (* jal 800011d8 <uvmcreate> *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x0e)%Z (mword_of_int 0xfbcff0ef : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x0e) : mword 64) (JAL (mword_of_int 2095036 : mword 21, Regidx (mword_of_int 1))) pptdec_0e. Qed.
  Lemma ppti_12 : PPT 0x12 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).  (* mv s1,a0 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x12)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) pptdec_12 exec_execute_C_MV. Qed.
  Lemma ppti_14 : PPT 0x14 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).  (* beqz a0,80001a5a *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x14)%Z (mword_of_int 0xcd05 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x14) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) pptdec_14 exec_execute_C_BEQZ. Qed.
  Lemma ppti_16 : PPT 0x16 true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,10 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x16)%Z (mword_of_int 0x4729 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) pptdec_16 exec_execute_C_LI. Qed.
  Lemma ppti_18 : PPT 0x18 false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 13), AUIPC)).  (* auipc a3,0x4 *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x18)%Z (mword_of_int 0x00004697 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x18) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 13), AUIPC)) pptdec_18. Qed.
  Lemma ppti_1c : PPT 0x1c false (ITYPE (mword_of_int 1498 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).  (* addi a3,a3,1498 # 80006000 <_trampoline> *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x1c)%Z (mword_of_int 0x5da68693 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x1c) : mword 64) (ITYPE (mword_of_int 1498 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) pptdec_1c. Qed.
  Lemma ppti_20 : PPT 0x20 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).  (* lui a2,0x1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x20)%Z (mword_of_int 0x6605 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x20) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) pptdec_20 exec_execute_C_LUI. Qed.
  Lemma ppti_22 : PPT 0x22 false (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)).  (* lui a1,0x4000 *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x22)%Z (mword_of_int 0x040005b7 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x22) : mword 64) (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)) pptdec_22. Qed.
  Lemma ppti_26 : PPT 0x26 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).  (* addi a1,a1,-1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x26)%Z (mword_of_int 0x15fd : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x26) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) pptdec_26 exec_execute_C_ADDI. Qed.
  Lemma ppti_28 : PPT 0x28 true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* slli a1,a1,0xc *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x28)%Z (mword_of_int 0x05b2 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x28) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) pptdec_28 exec_execute_C_SLLI. Qed.
  Lemma ppti_2a : PPT 0x2a false (JAL (mword_of_int 2094584 : mword 21, Regidx (mword_of_int 1))).  (* jal 80001030 <mappages> *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x2a)%Z (mword_of_int 0xdf8ff0ef : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x2a) : mword 64) (JAL (mword_of_int 2094584 : mword 21, Regidx (mword_of_int 1))) pptdec_2a. Qed.
  Lemma ppti_2e : PPT 0x2e false (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).  (* bltz a0,80001a68 *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x2e)%Z (mword_of_int 0x02054663 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x2e) : mword 64) (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) pptdec_2e. Qed.
  Lemma ppti_32 : PPT 0x32 true (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).  (* li a4,6 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x32)%Z (mword_of_int 0x4719 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x32) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 6 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) pptdec_32 exec_execute_C_LI. Qed.
  Lemma ppti_34 : PPT 0x34 false (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 13), false, 8)).  (* ld a3,88(s2) *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x34)%Z (mword_of_int 0x05893683 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x34) : mword 64) (LOAD (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 13), false, 8)) pptdec_34. Qed.
  Lemma ppti_38 : PPT 0x38 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).  (* lui a2,0x1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x38)%Z (mword_of_int 0x6605 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x38) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) pptdec_20 exec_execute_C_LUI. Qed.
  Lemma ppti_3a : PPT 0x3a false (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 11), LUI)).  (* lui a1,0x2000 *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x3a)%Z (mword_of_int 0x020005b7 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x3a) : mword 64) (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 11), LUI)) pptdec_3a. Qed.
  Lemma ppti_3e : PPT 0x3e true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).  (* addi a1,a1,-1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x3e)%Z (mword_of_int 0x15fd : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) pptdec_26 exec_execute_C_ADDI. Qed.
  Lemma ppti_40 : PPT 0x40 true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* slli a1,a1,0xd *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x40)%Z (mword_of_int 0x05b6 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x40) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) pptdec_40 exec_execute_C_SLLI. Qed.
  Lemma ppti_42 : PPT 0x42 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x42)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) pptdec_42 exec_execute_C_MV. Qed.
  Lemma ppti_44 : PPT 0x44 false (JAL (mword_of_int 2094558 : mword 21, Regidx (mword_of_int 1))).  (* jal 80001030 <mappages> *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x44)%Z (mword_of_int 0xddeff0ef : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x44) : mword 64) (JAL (mword_of_int 2094558 : mword 21, Regidx (mword_of_int 1))) pptdec_44. Qed.
  Lemma ppti_48 : PPT 0x48 false (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).  (* bltz a0,80001a74 *)
  Proof. mk_base (KernelSyms.proc_pagetable + 0x48)%Z (mword_of_int 0x00054f63 : mword 32) (mword_of_int (KernelSyms.proc_pagetable + 0x48) : mword 64) (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) pptdec_48. Qed.
  Lemma ppti_4c : PPT 0x4c true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x4c)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) pptdec_42 exec_execute_C_MV. Qed.
  Lemma ppti_4e : PPT 0x4e true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x4e)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x4e) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)) pptdec_4e exec_execute_C_LDSP. Qed.
  Lemma ppti_50 : PPT 0x50 true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x50)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x50) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)) pptdec_50 exec_execute_C_LDSP. Qed.
  Lemma ppti_52 : PPT 0x52 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)).  (* ld s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x52)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x52) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)) pptdec_52 exec_execute_C_LDSP. Qed.
  Lemma ppti_54 : PPT 0x54 true (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 18), false, 8)).  (* ld s2,0(sp) *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x54)%Z (mword_of_int 0x6902 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x54) : mword 64) (LOAD (csdsp_imm 0, sp, Regidx (mword_of_int 18), false, 8)) pptdec_54 exec_execute_C_LDSP. Qed.
  Lemma ppti_56 : PPT 0x56 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).  (* addi sp,sp,32 *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x56)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x56) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) pptdec_56 exec_execute_C_ADDI16SP. Qed.
  Lemma ppti_58 : PPT 0x58 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.proc_pagetable + 0x58)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.proc_pagetable + 0x58) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) pptdec_58 exec_execute_C_JR. Qed.

End ProcPagetableInstrs.

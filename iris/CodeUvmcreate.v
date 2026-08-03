(* CodeUvmcreate.v -- decode catalog for xv6's uvmcreate() (kernel/vm.c),
   the whole function: KernelInstrs.v bytes at KernelSyms.uvmcreate
   (0x800011d8 .. 0x800011fc, 17 instrs) -- the 4-slot frame (addi sp,-32;
   ra/s0/s1 saves), the kalloc jal, the null test, the memset jal and the
   epilogue.  Same architecture as CodeKvmmake.v: per-instruction decode
   facts plus the [instr] constructors, consumed by the wp_uvmcreate proof.
   JAL residues = (target - pc) mod 2^21. *)
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

Section UvmcreateInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation UVC off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.uvmcreate + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).

  (* ---- decode facts ---- *)
  Lemma uvcdec_00 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x1101 : mword 16)) s
    = Some (C_ADDI (mword_of_int 32, Regidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xec06 : mword 16)) s
    = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_04 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe822 : mword 16)) s
    = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xe426 : mword 16)) s
    = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_08 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x1000 : mword 16)) s
    = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 8), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_0a s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0x94dff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095436 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma uvcdec_0e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x84aa : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 10)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_10 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0xc509 : mword 16)) s
    = Some (C_BEQZ (mword_of_int 5, Cregidx (mword_of_int 2)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_12 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6605 : mword 16)) s
    = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 12)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_14 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x4581 : mword 16)) s
    = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 11)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_16 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xadbff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2095834 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
  Lemma uvcdec_1a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
    = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_1c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x60e2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_1e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6442 : mword 16)) s
    = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 8)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_20 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x64a2 : mword 16)) s
    = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 9)), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_22 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x6105 : mword 16)) s
    = Some (C_ADDI16SP (mword_of_int 2), s).
  Proof. intro H. rvc_oneshot s H. Qed.
  Lemma uvcdec_24 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
    exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
    = Some (C_JR (Regidx (mword_of_int 1)), s).
  Proof. intro H. rvc_oneshot s H. Qed.

  (* ---- instr lemmas ---- *)
  Lemma uvci_00 : UVC 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)).  (* addi sp,sp,-32 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx (mword_of_int 2), Regidx (mword_of_int 2), ADDI)) uvcdec_00 exec_execute_C_ADDI. Qed.
  Lemma uvci_02 : UVC 0x02 true (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)).  (* sd ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x02) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 1), sp, 8)) uvcdec_02 exec_execute_C_SDSP. Qed.
  Lemma uvci_04 : UVC 0x04 true (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)).  (* sd s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x04) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 8), sp, 8)) uvcdec_04 exec_execute_C_SDSP. Qed.
  Lemma uvci_06 : UVC 0x06 true (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)).  (* sd s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x06) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 9), sp, 8)) uvcdec_06 exec_execute_C_SDSP. Qed.
  Lemma uvci_08 : UVC 0x08 true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi s0,sp,32 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x08)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) uvcdec_08 exec_execute_C_ADDI4SPN. Qed.
  Lemma uvci_0a : UVC 0x0a false (JAL (mword_of_int 2095436 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000b2e <kalloc> *)
  Proof. mk_base (KernelSyms.uvmcreate + 0x0a)%Z (mword_of_int 0x94dff0ef : mword 32) (mword_of_int (KernelSyms.uvmcreate + 0x0a) : mword 64) (JAL (mword_of_int 2095436 : mword 21, Regidx (mword_of_int 1))) uvcdec_0a. Qed.
  Lemma uvci_0e : UVC 0x0e true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).  (* mv s1,a0 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x0e)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) uvcdec_0e exec_execute_C_MV. Qed.
  Lemma uvci_10 : UVC 0x10 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).  (* beqz a0,800011f2 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x10)%Z (mword_of_int 0xc509 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x10) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) uvcdec_10 exec_execute_C_BEQZ. Qed.
  Lemma uvci_12 : UVC 0x12 true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).  (* lui a2,0x1 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x12)%Z (mword_of_int 0x6605 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x12) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) uvcdec_12 exec_execute_C_LUI. Qed.
  Lemma uvci_14 : UVC 0x14 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).  (* li a1,0 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x14)%Z (mword_of_int 0x4581 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) uvcdec_14 exec_execute_C_LI. Qed.
  Lemma uvci_16 : UVC 0x16 false (JAL (mword_of_int 2095834 : mword 21, Regidx (mword_of_int 1))).  (* jal 80000cc8 <memset> *)
  Proof. mk_base (KernelSyms.uvmcreate + 0x16)%Z (mword_of_int 0xadbff0ef : mword 32) (mword_of_int (KernelSyms.uvmcreate + 0x16) : mword 64) (JAL (mword_of_int 2095834 : mword 21, Regidx (mword_of_int 1))) uvcdec_16. Qed.
  Lemma uvci_1a : UVC 0x1a true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* mv a0,s1 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x1a)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) uvcdec_1a exec_execute_C_MV. Qed.
  Lemma uvci_1c : UVC 0x1c true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)).  (* ld ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x1c)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x1c) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 1), false, 8)) uvcdec_1c exec_execute_C_LDSP. Qed.
  Lemma uvci_1e : UVC 0x1e true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)).  (* ld s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x1e)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x1e) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 8), false, 8)) uvcdec_1e exec_execute_C_LDSP. Qed.
  Lemma uvci_20 : UVC 0x20 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)).  (* ld s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x20)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x20) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 9), false, 8)) uvcdec_20 exec_execute_C_LDSP. Qed.
  Lemma uvci_22 : UVC 0x22 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).  (* addi sp,sp,32 *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x22)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x22) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) uvcdec_22 exec_execute_C_ADDI16SP. Qed.
  Lemma uvci_24 : UVC 0x24 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.uvmcreate + 0x24)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.uvmcreate + 0x24) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) uvcdec_24 exec_execute_C_JR. Qed.

End UvmcreateInstrs.

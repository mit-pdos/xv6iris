(* CodeUartinit.v -- the instruction-DECODE layer for xv6's uartinit().
   For every instruction of

     uartinit @ 0x80000886 .. 0x800008da   (offsets 0x00 .. 0x54)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([uii_<off>]).  The
   16-byte-frame prologue/epilogue compressed encodings reuse the shared
   [cdec_*] helpers from KernelRvcDecode (identical to kinit); the LUI/SB/AUIPC/
   ADDI/JAL base words and the c.li/c.mv get fresh decode helpers here. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to uartinit (c.li a3,3 / c.li a2,7 /    *)
(* c.mv a4,a2).                                                            *)
(* ===================================================================== *)
Lemma uidc_468d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x468d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma uidc_461d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x461d : mword 16)) s
  = Some (C_LI (mword_of_int 7, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.





Lemma uidb_f8000693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8000693 : mword 32)) s
  = Some (ITYPE (mword_of_int 3968 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 13), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_000780a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000780a3 : mword 32)) s
  = Some (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_00d701a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d701a3 : mword 32)) s
  = Some (STORE (mword_of_int 3 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_00d60023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d60023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_00c70123 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c70123 : mword 32)) s
  = Some (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 1), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_00d780a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d780a3 : mword 32)) s
  = Some (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.


Lemma uidb_77058593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x77058593 : mword 32)) s
  = Some (ITYPE (mword_of_int 1904 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.


Lemma uidb_a4850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa4850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2632 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma uidb_2b8000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2b8000ef : mword 32)) s
  = Some (JAL (mword_of_int 696 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section CodeUartinit.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation UI := KernelSyms.uartinit.

  (* --- prologue (0x00..0x06): shared cdec_* helpers, as in kinit --- *)
  Lemma uii_00 : kernel_text -∗ instr (mword_of_int (UI + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UI + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (UI + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma uii_02 : kernel_text -∗ instr (mword_of_int (UI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (UI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma uii_04 : kernel_text -∗ instr (mword_of_int (UI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (UI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma uii_06 : kernel_text -∗ instr (mword_of_int (UI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (UI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* --- body (0x08..0x36): LUI/SB/ADDI/c.li/c.mv --- *)
  Lemma uii_08 : kernel_text -∗ instr (mword_of_int (UI + 0x08) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)).
  Proof. mk_base (UI + 0x08)%Z (mword_of_int 0x100007b7 : mword 32)
    (mword_of_int (UI + 0x08) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 15), LUI)) bdec_100007b7. Qed.

  Lemma uii_0c : kernel_text -∗ instr (mword_of_int (UI + 0x0c) : mword 64) false (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (UI + 0x0c)%Z (mword_of_int 0x000780a3 : mword 32)
    (mword_of_int (UI + 0x0c) : mword 64) (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)) uidb_000780a3. Qed.

  Lemma uii_10 : kernel_text -∗ instr (mword_of_int (UI + 0x10) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (UI + 0x10)%Z (mword_of_int 0x10000737 : mword 32)
    (mword_of_int (UI + 0x10) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 14), LUI)) bdec_10000737. Qed.

  Lemma uii_14 : kernel_text -∗ instr (mword_of_int (UI + 0x14) : mword 64) false (ITYPE (mword_of_int 3968 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 13), ADDI)).
  Proof. mk_base (UI + 0x14)%Z (mword_of_int 0xf8000693 : mword 32)
    (mword_of_int (UI + 0x14) : mword 64) (ITYPE (mword_of_int 3968 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 13), ADDI)) uidb_f8000693. Qed.

  Lemma uii_18 : kernel_text -∗ instr (mword_of_int (UI + 0x18) : mword 64) false (STORE (mword_of_int 3 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)).
  Proof. mk_base (UI + 0x18)%Z (mword_of_int 0x00d701a3 : mword 32)
    (mword_of_int (UI + 0x18) : mword 64) (STORE (mword_of_int 3 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)) uidb_00d701a3. Qed.

  Lemma uii_1c : kernel_text -∗ instr (mword_of_int (UI + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (UI + 0x1c)%Z (mword_of_int 0x468d : mword 16)
    (mword_of_int (UI + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) uidc_468d exec_execute_C_LI. Qed.

  Lemma uii_1e : kernel_text -∗ instr (mword_of_int (UI + 0x1e) : mword 64) false (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 12), LUI)).
  Proof. mk_base (UI + 0x1e)%Z (mword_of_int 0x10000637 : mword 32)
    (mword_of_int (UI + 0x1e) : mword 64) (UTYPE (mword_of_int 0x10000 : mword 20, Regidx (mword_of_int 12), LUI)) bdec_10000637. Qed.

  Lemma uii_22 : kernel_text -∗ instr (mword_of_int (UI + 0x22) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), 1)).
  Proof. mk_base (UI + 0x22)%Z (mword_of_int 0x00d60023 : mword 32)
    (mword_of_int (UI + 0x22) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), 1)) uidb_00d60023. Qed.

  Lemma uii_26 : kernel_text -∗ instr (mword_of_int (UI + 0x26) : mword 64) false (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (UI + 0x26)%Z (mword_of_int 0x000780a3 : mword 32)
    (mword_of_int (UI + 0x26) : mword 64) (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)) uidb_000780a3. Qed.

  Lemma uii_2a : kernel_text -∗ instr (mword_of_int (UI + 0x2a) : mword 64) false (STORE (mword_of_int 3 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)).
  Proof. mk_base (UI + 0x2a)%Z (mword_of_int 0x00d701a3 : mword 32)
    (mword_of_int (UI + 0x2a) : mword 64) (STORE (mword_of_int 3 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 1)) uidb_00d701a3. Qed.

  Lemma uii_2e : kernel_text -∗ instr (mword_of_int (UI + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (UI + 0x2e)%Z (mword_of_int 0x8732 : mword 16)
    (mword_of_int (UI + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 14), ADD)) cdec_8732 exec_execute_C_MV. Qed.

  Lemma uii_30 : kernel_text -∗ instr (mword_of_int (UI + 0x30) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (UI + 0x30)%Z (mword_of_int 0x461d : mword 16)
    (mword_of_int (UI + 0x30) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 7 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) uidc_461d exec_execute_C_LI. Qed.

  Lemma uii_32 : kernel_text -∗ instr (mword_of_int (UI + 0x32) : mword 64) false (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 1)).
  Proof. mk_base (UI + 0x32)%Z (mword_of_int 0x00c70123 : mword 32)
    (mword_of_int (UI + 0x32) : mword 64) (STORE (mword_of_int 2 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 14), 1)) uidb_00c70123. Qed.

  Lemma uii_36 : kernel_text -∗ instr (mword_of_int (UI + 0x36) : mword 64) false (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (UI + 0x36)%Z (mword_of_int 0x00d780a3 : mword 32)
    (mword_of_int (UI + 0x36) : mword 64) (STORE (mword_of_int 1 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 1)) uidb_00d780a3. Qed.

  (* --- args (0x3a..0x46): auipc/addi for a1="uart", a0=&tx_lock --- *)
  Lemma uii_3a : kernel_text -∗ instr (mword_of_int (UI + 0x3a) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (UI + 0x3a)%Z (mword_of_int 0x00006597 : mword 32)
    (mword_of_int (UI + 0x3a) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00006597. Qed.

  Lemma uii_3e : kernel_text -∗ instr (mword_of_int (UI + 0x3e) : mword 64) false (ITYPE (mword_of_int 1904 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (UI + 0x3e)%Z (mword_of_int 0x77058593 : mword 32)
    (mword_of_int (UI + 0x3e) : mword 64) (ITYPE (mword_of_int 1904 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) uidb_77058593. Qed.

  Lemma uii_42 : kernel_text -∗ instr (mword_of_int (UI + 0x42) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UI + 0x42)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (UI + 0x42) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma uii_46 : kernel_text -∗ instr (mword_of_int (UI + 0x46) : mword 64) false (ITYPE (mword_of_int 2632 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UI + 0x46)%Z (mword_of_int 0xa4850513 : mword 32)
    (mword_of_int (UI + 0x46) : mword 64) (ITYPE (mword_of_int 2632 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uidb_a4850513. Qed.

  (* --- jal initlock (0x4a) --- *)
  Lemma uii_4a : kernel_text -∗ instr (mword_of_int (UI + 0x4a) : mword 64) false (JAL (mword_of_int 696 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UI + 0x4a)%Z (mword_of_int 0x2b8000ef : mword 32)
    (mword_of_int (UI + 0x4a) : mword 64) (JAL (mword_of_int 696 : mword 21, Regidx (mword_of_int 1))) uidb_2b8000ef. Qed.

  (* --- epilogue (0x4e..0x54): shared cdec_* helpers, as in kinit --- *)
  Lemma uii_4e : kernel_text -∗ instr (mword_of_int (UI + 0x4e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UI + 0x4e)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (UI + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma uii_50 : kernel_text -∗ instr (mword_of_int (UI + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UI + 0x50)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (UI + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma uii_52 : kernel_text -∗ instr (mword_of_int (UI + 0x52) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UI + 0x52)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (UI + 0x52) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma uii_54 : kernel_text -∗ instr (mword_of_int (UI + 0x54) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UI + 0x54)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UI + 0x54) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeUartinit.

(* WpArgstrDecode.v -- the instruction-DECODE layer for xv6's argstr().

     argstr @ 0x8000283c .. 0x80002863   (offsets 0x00 .. 0x26, 40 bytes)

   One [kernel_text -* instr pc <is_rvc> <AST>] fact ([asi_<off>]) per
   instruction plus the decode facts they consume; only two words are argstr's
   own (both [c.mv]s) and the rest come from KernelRvcDecode.

   STRAIGHT LINE, no branch at all -- and note that argaddr is INLINED: the C
   is [argaddr(n, &addr); return fetchstr(addr, buf, max);] but there is no
   [uint64 addr] on the stack and no call to argaddr, only a [jal argraw]
   whose a0 is handed straight to fetchstr.  So the frame is 4 slots (all
   used: ra/s0/s1=max/s2=buf) and the ASYMMETRIC push/pop pattern applies --
   [c.addi sp,-32] pushes but [c.addi16sp sp,32] pops.                       *)
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
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for this function's own words.                 *)
(* ===================================================================== *)

(* c.mv s1,a2          # s1 := max *)
Lemma asdc_84b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84b2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a2,s1 *)
Lemma asdc_8626 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8626 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* jal ra,argraw       # -306 -> 0x8000271a *)
Lemma asdb_ecfff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xecfff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096846 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,fetchstr     # -144 -> 0x800027c4 *)
Lemma asdb_f71ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf71ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2097008 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InstrsAS.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma asi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).  (* c.addi sp,sp,-32    # 32-byte frame: ra/s0/s1/s2 *)
  Proof. mk_rvc (KernelSyms.argstr + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma asi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma asi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma asi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* c.sdsp s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma asi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* c.sdsp s2,0(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma asi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,32 *)
  Proof. mk_rvc (KernelSyms.argstr + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma asi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).  (* c.mv s2,a1          # s2 := buf *)
  Proof. mk_rvc (KernelSyms.argstr + 0x0c)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma asi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,a2          # s1 := max *)
  Proof. mk_rvc (KernelSyms.argstr + 0x0e)%Z (mword_of_int 0x84b2 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)) asdc_84b2 exec_execute_C_MV. Qed.

  Lemma asi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x10) : mword 64) false (JAL (mword_of_int 2096846 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,argraw       # -306 -> 0x8000271a *)
  Proof. mk_base (KernelSyms.argstr + 0x10)%Z (mword_of_int 0xecfff0ef : mword 32)
    (mword_of_int (KernelSyms.argstr + 0x10) : mword 64) (JAL (mword_of_int 2096846 : mword 21, Regidx (mword_of_int 1))) asdb_ecfff0ef. Qed.

  Lemma asi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 12), ADD)).  (* c.mv a2,s1 *)
  Proof. mk_rvc (KernelSyms.argstr + 0x14)%Z (mword_of_int 0x8626 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 12), ADD)) asdc_8626 exec_execute_C_MV. Qed.

  Lemma asi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s2 *)
  Proof. mk_rvc (KernelSyms.argstr + 0x16)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma asi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x18) : mword 64) false (JAL (mword_of_int 2097008 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,fetchstr     # -144 -> 0x800027c4 *)
  Proof. mk_base (KernelSyms.argstr + 0x18)%Z (mword_of_int 0xf71ff0ef : mword 32)
    (mword_of_int (KernelSyms.argstr + 0x18) : mword 64) (JAL (mword_of_int 2097008 : mword 21, Regidx (mword_of_int 1))) asdb_f71ff0ef. Qed.

  Lemma asi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,24(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x1c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma asi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,16(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x1e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma asi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* c.ldsp s1,8(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x20)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma asi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* c.ldsp s2,0(sp) *)
  Proof. mk_rvc (KernelSyms.argstr + 0x22)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma asi_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x24) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,32 *)
  Proof. mk_rvc (KernelSyms.argstr + 0x24)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x24) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma asi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.argstr + 0x26) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (KernelSyms.argstr + 0x26)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.argstr + 0x26) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End InstrsAS.


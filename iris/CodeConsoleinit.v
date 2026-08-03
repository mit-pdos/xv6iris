(* CodeConsoleinit.v -- the instruction-DECODE layer for xv6's consoleinit().
   For every instruction of

     consoleinit @ 0x80000422 .. 0x80000464   (offsets 0x00 .. 0x42)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([cii_<off>]) plus
   the per-instruction decode facts they consume ([cidc_<word>] compressed /
   [cidb_<word>] base).

   consoleinit uses the standard 16-byte / 2-slot frame, so every frame word is
   one of the shared [cdec_*] templates in KernelRvcDecode.v, and the auipc a0
   word it shares with printkinit/kinit/uartinit comes from KernelBaseDecode.v.
   Everything else -- the four relocated addi immediates, the two jal
   displacements, the three remaining auipc words and the two [c.sd]s into
   devsw[] -- carries consoleinit's own encodings and is proved here.

   As in CodeBinit.v, the two compressed [c.sd]s are the only ASTs needing
   massaging: the RVC expansion yields a STORE over [creg2reg_idx] register
   indices and a [zero_extend'] of the scaled 5-bit offset, while the
   [wp_csd_s_sconf] leaf wants plain [Regidx]es and a 12-bit immediate.  Both
   forms are convertible, so the bridge is four [vm_compute] equations
   rewritten into the goal before [mk_rvc] runs -- done HERE so consoleinit's
   proof only ever sees the leaf's shape. *)
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to consoleinit.                         *)
(* ===================================================================== *)

(* 0xeb98  c.sd a4,16(a5) *)
Lemma cidc_eb98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeb98 : mword 16)) s
  = Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xef98  c.sd a4,24(a5) *)
Lemma cidc_ef98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xef98 : mword 16)) s
  = Some (C_SD (mword_of_int 3, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to consoleinit.  The negative addi    *)
(* immediates appear as the decoder's POSITIVE RESIDUE (-1066 -> 3030, …). *)
(* ===================================================================== *)

(* auipc a1,0x7 -- a1 := &"cons" (high part) *)
Lemma cidb_00007597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00007597 : mword 32)) s
  = Some (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,a1,-1066 -- a1 := &"cons" *)
Lemma cidb_bd658593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbd658593 : mword 32)) s
  = Some (ITYPE (mword_of_int 3030 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,-482 -- a0 := &cons (= &cons.lock) *)
Lemma cidb_e1e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe1e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3614 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initlock *)
Lemma cidb_74e000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x74e000ef : mword 32)) s
  = Some (JAL (mword_of_int 1870 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,uartinit *)
Lemma cidb_448000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x448000ef : mword 32)) s
  = Some (JAL (mword_of_int 1096 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* auipc a5,0x22 -- a5 := &devsw (high part) *)
Lemma cidb_00022797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00022797 : mword 32)) s
  = Some (UTYPE (mword_of_int 34 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a5,-130 -- a5 := &devsw *)
Lemma cidb_f7e78793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf7e78793 : mword 32)) s
  = Some (ITYPE (mword_of_int 3966 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a4,0x0 -- both function-pointer materializations start here *)
Lemma cidb_00000717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00000717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a4,a4,-722 -- a4 := consoleread *)
Lemma cidb_d2e70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd2e70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 3374 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a4,a4,-894 -- a4 := consolewrite *)
Lemma cidb_c8270713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc8270713 : mword 32)) s
  = Some (ITYPE (mword_of_int 3202 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(* The c.sd AST bridge: scaled-uimm -> 12-bit immediate, Cregidx -> Regidx *)
(* ===================================================================== *)

Lemma cid_csd_imm16 :
  zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")) = (mword_of_int 16 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma cid_csd_imm24 :
  zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")) = (mword_of_int 24 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Section CodeConsoleinit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation CI := KernelSyms.consoleinit.

  (* ---- prologue: 2-slot frame push, save ra/s0, set up s0 ---- *)

  Lemma cii_00 : kernel_text -∗ instr (mword_of_int CI : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc CI (mword_of_int 0x1141 : mword 16)
    (mword_of_int CI : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma cii_02 : kernel_text -∗ instr (mword_of_int (CI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (CI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (CI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma cii_04 : kernel_text -∗ instr (mword_of_int (CI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (CI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (CI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma cii_06 : kernel_text -∗ instr (mword_of_int (CI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (CI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (CI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- initlock(&cons.lock, "cons") ---- *)

  Lemma cii_08 : kernel_text -∗ instr (mword_of_int (CI + 0x08) : mword 64) false (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (CI + 0x08)%Z (mword_of_int 0x00007597 : mword 32)
    (mword_of_int (CI + 0x08) : mword 64) (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 11), AUIPC)) cidb_00007597. Qed.

  Lemma cii_0c : kernel_text -∗ instr (mword_of_int (CI + 0x0c) : mword 64) false (ITYPE (mword_of_int 3030 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (CI + 0x0c)%Z (mword_of_int 0xbd658593 : mword 32)
    (mword_of_int (CI + 0x0c) : mword 64) (ITYPE (mword_of_int 3030 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) cidb_bd658593. Qed.

  Lemma cii_10 : kernel_text -∗ instr (mword_of_int (CI + 0x10) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (CI + 0x10)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (CI + 0x10) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma cii_14 : kernel_text -∗ instr (mword_of_int (CI + 0x14) : mword 64) false (ITYPE (mword_of_int 3614 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (CI + 0x14)%Z (mword_of_int 0xe1e50513 : mword 32)
    (mword_of_int (CI + 0x14) : mword 64) (ITYPE (mword_of_int 3614 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) cidb_e1e50513. Qed.

  Lemma cii_18 : kernel_text -∗ instr (mword_of_int (CI + 0x18) : mword 64) false (JAL (mword_of_int 1870 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x18)%Z (mword_of_int 0x74e000ef : mword 32)
    (mword_of_int (CI + 0x18) : mword 64) (JAL (mword_of_int 1870 : mword 21, Regidx (mword_of_int 1))) cidb_74e000ef. Qed.

  (* ---- uartinit() ---- *)

  Lemma cii_1c : kernel_text -∗ instr (mword_of_int (CI + 0x1c) : mword 64) false (JAL (mword_of_int 1096 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (CI + 0x1c)%Z (mword_of_int 0x448000ef : mword 32)
    (mword_of_int (CI + 0x1c) : mword 64) (JAL (mword_of_int 1096 : mword 21, Regidx (mword_of_int 1))) cidb_448000ef. Qed.

  (* ---- devsw[CONSOLE].read = consoleread; .write = consolewrite ---- *)

  Lemma cii_20 : kernel_text -∗ instr (mword_of_int (CI + 0x20) : mword 64) false (UTYPE (mword_of_int 34 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (CI + 0x20)%Z (mword_of_int 0x00022797 : mword 32)
    (mword_of_int (CI + 0x20) : mword 64) (UTYPE (mword_of_int 34 : mword 20, Regidx (mword_of_int 15), AUIPC)) cidb_00022797. Qed.

  Lemma cii_24 : kernel_text -∗ instr (mword_of_int (CI + 0x24) : mword 64) false (ITYPE (mword_of_int 3966 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (CI + 0x24)%Z (mword_of_int 0xf7e78793 : mword 32)
    (mword_of_int (CI + 0x24) : mword 64) (ITYPE (mword_of_int 3966 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cidb_f7e78793. Qed.

  Lemma cii_28 : kernel_text -∗ instr (mword_of_int (CI + 0x28) : mword 64) false (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (CI + 0x28)%Z (mword_of_int 0x00000717 : mword 32)
    (mword_of_int (CI + 0x28) : mword 64) (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 14), AUIPC)) cidb_00000717. Qed.

  Lemma cii_2c : kernel_text -∗ instr (mword_of_int (CI + 0x2c) : mword 64) false (ITYPE (mword_of_int 3374 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (CI + 0x2c)%Z (mword_of_int 0xd2e70713 : mword 32)
    (mword_of_int (CI + 0x2c) : mword 64) (ITYPE (mword_of_int 3374 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) cidb_d2e70713. Qed.

  Lemma cii_30 : kernel_text -∗ instr (mword_of_int (CI + 0x30) : mword 64) true (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)).
  Proof.
    rewrite -cid_csd_imm16 -creg_c6 -creg_c7.
    mk_rvc (CI + 0x30)%Z (mword_of_int 0xeb98 : mword 16)
      (mword_of_int (CI + 0x30) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), 8)) cidc_eb98 exec_execute_C_SD.
  Qed.

  Lemma cii_32 : kernel_text -∗ instr (mword_of_int (CI + 0x32) : mword 64) false (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (CI + 0x32)%Z (mword_of_int 0x00000717 : mword 32)
    (mword_of_int (CI + 0x32) : mword 64) (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 14), AUIPC)) cidb_00000717. Qed.

  Lemma cii_36 : kernel_text -∗ instr (mword_of_int (CI + 0x36) : mword 64) false (ITYPE (mword_of_int 3202 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (CI + 0x36)%Z (mword_of_int 0xc8270713 : mword 32)
    (mword_of_int (CI + 0x36) : mword 64) (ITYPE (mword_of_int 3202 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) cidb_c8270713. Qed.

  Lemma cii_3a : kernel_text -∗ instr (mword_of_int (CI + 0x3a) : mword 64) true (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 8)).
  Proof.
    rewrite -cid_csd_imm24 -creg_c6 -creg_c7.
    mk_rvc (CI + 0x3a)%Z (mword_of_int 0xef98 : mword 16)
      (mword_of_int (CI + 0x3a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), 8)) cidc_ef98 exec_execute_C_SD.
  Qed.

  (* ---- epilogue: restore ra/s0, frame pop, ret ---- *)

  Lemma cii_3c : kernel_text -∗ instr (mword_of_int (CI + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (CI + 0x3c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (CI + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma cii_3e : kernel_text -∗ instr (mword_of_int (CI + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (CI + 0x3e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (CI + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma cii_40 : kernel_text -∗ instr (mword_of_int (CI + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (CI + 0x40)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (CI + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma cii_42 : kernel_text -∗ instr (mword_of_int (CI + 0x42) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (CI + 0x42)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (CI + 0x42) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeConsoleinit.

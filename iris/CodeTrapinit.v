(* CodeTrapinit.v -- the instruction-DECODE layer for xv6's trapinit().
   For every instruction of

     trapinit @ 0x80002402 .. 0x80002424   (offsets 0x00 .. 0x22)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([tri_<off>]), and
   bundles the thirteen of them into the [ilw_code] pattern
   ([SpecInitlockWrapper.v]) that trapinit's whole-function proof instantiates.

   trapinit is a thin initlock wrapper on the standard 16-byte frame, so every
   compressed word is one of the shared [cdec_*] templates from
   KernelRvcDecode; only the five base words carrying trapinit's own relocated
   immediates (two auipc's, two addi's, and the jal to initlock) need fresh
   decode helpers, and each is used by this function alone. *)
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
Require Import KernelRvcDecode.
Require Import KernelBaseDecode.
Require Import SpecInitlockWrapper.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to trapinit.                        *)
(* ===================================================================== *)

(* addi a1,a1,-450  -- a1 := &"time"  (the decoder's positive residue: 4096-450) *)
Lemma tdb_e3e58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe3e58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 3646 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x16 *)
Lemma tdb_00016517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00016517 : mword 32)) s
  = Some (UTYPE (mword_of_int 22 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,-666  -- a0 := &tickslock  (4096-666) *)
Lemma tdb_d6650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd6650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3430 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initlock  (backwards: 2^21 - 6290) *)
Lemma tdb_f6efe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf6efe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2090862 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section CodeTrapinit.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation TI := KernelSyms.trapinit.

  Lemma tri_00 : kernel_text -∗ instr (mword_of_int TI : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc TI (mword_of_int 0x1141 : mword 16)
    (mword_of_int TI : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma tri_02 : kernel_text -∗ instr (mword_of_int (TI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (TI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (TI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma tri_04 : kernel_text -∗ instr (mword_of_int (TI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (TI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (TI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma tri_06 : kernel_text -∗ instr (mword_of_int (TI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (TI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (TI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma tri_08 : kernel_text -∗ instr (mword_of_int (TI + 0x08) : mword 64) false (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (TI + 0x08)%Z (mword_of_int 0x00005597 : mword 32)
    (mword_of_int (TI + 0x08) : mword 64) (UTYPE (mword_of_int 5 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00005597. Qed.

  Lemma tri_0c : kernel_text -∗ instr (mword_of_int (TI + 0x0c) : mword 64) false (ITYPE (mword_of_int 3646 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (TI + 0x0c)%Z (mword_of_int 0xe3e58593 : mword 32)
    (mword_of_int (TI + 0x0c) : mword 64) (ITYPE (mword_of_int 3646 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) tdb_e3e58593. Qed.

  Lemma tri_10 : kernel_text -∗ instr (mword_of_int (TI + 0x10) : mword 64) false (UTYPE (mword_of_int 22 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (TI + 0x10)%Z (mword_of_int 0x00016517 : mword 32)
    (mword_of_int (TI + 0x10) : mword 64) (UTYPE (mword_of_int 22 : mword 20, Regidx (mword_of_int 10), AUIPC)) tdb_00016517. Qed.

  Lemma tri_14 : kernel_text -∗ instr (mword_of_int (TI + 0x14) : mword 64) false (ITYPE (mword_of_int 3430 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (TI + 0x14)%Z (mword_of_int 0xd6650513 : mword 32)
    (mword_of_int (TI + 0x14) : mword 64) (ITYPE (mword_of_int 3430 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) tdb_d6650513. Qed.

  Lemma tri_18 : kernel_text -∗ instr (mword_of_int (TI + 0x18) : mword 64) false (JAL (mword_of_int 2090862 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (TI + 0x18)%Z (mword_of_int 0xf6efe0ef : mword 32)
    (mword_of_int (TI + 0x18) : mword 64) (JAL (mword_of_int 2090862 : mword 21, Regidx (mword_of_int 1))) tdb_f6efe0ef. Qed.

  Lemma tri_1c : kernel_text -∗ instr (mword_of_int (TI + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (TI + 0x1c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (TI + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma tri_1e : kernel_text -∗ instr (mword_of_int (TI + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (TI + 0x1e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (TI + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma tri_20 : kernel_text -∗ instr (mword_of_int (TI + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (TI + 0x20)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (TI + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma tri_22 : kernel_text -∗ instr (mword_of_int (TI + 0x22) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (TI + 0x22)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (TI + 0x22) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* trapinit's thirteen instructions, in the thin-initlock-wrapper pattern.
     The five immediates are exactly what the whole-function proof needs to
     know about trapinit's code. *)
  Lemma tri_code :
    kernel_text -∗ ilw_code TI (mword_of_int 5) (mword_of_int 22)
                            (mword_of_int 3646) (mword_of_int 3430) (mword_of_int 2090862).
  Proof.
    iIntros "#Ht". rewrite /ilw_code.
    iSplitR; [iApply (tri_00 with "Ht")|].
    iSplitR; [iApply (tri_02 with "Ht")|].
    iSplitR; [iApply (tri_04 with "Ht")|].
    iSplitR; [iApply (tri_06 with "Ht")|].
    iSplitR; [iApply (tri_08 with "Ht")|].
    iSplitR; [iApply (tri_0c with "Ht")|].
    iSplitR; [iApply (tri_10 with "Ht")|].
    iSplitR; [iApply (tri_14 with "Ht")|].
    iSplitR; [iApply (tri_18 with "Ht")|].
    iSplitR; [iApply (tri_1c with "Ht")|].
    iSplitR; [iApply (tri_1e with "Ht")|].
    iSplitR; [iApply (tri_20 with "Ht")|].
    iApply (tri_22 with "Ht").
  Qed.

End CodeTrapinit.

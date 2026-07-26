(* WpFileinitDecode.v -- the instruction-DECODE layer for xv6's fileinit().
   For every instruction of

     fileinit @ 0x80003f94 .. 0x80003fb6   (offsets 0x00 .. 0x22)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fii_<off>]), and
   bundles the thirteen of them into the [ilw_code] pattern
   ([SpecInitlockWrapper.v]) that fileinit's whole-function proof instantiates.

   fileinit is a thin initlock wrapper on the standard 16-byte frame, so every
   compressed word is one of the shared [mdec_*] templates from
   KernelRvcDecode; only the five base words carrying fileinit's own relocated
   immediates (two auipc's, two addi's, and the jal to initlock) need fresh
   decode helpers, and each is used by this function alone.  Both addi
   immediates are POSITIVE here, so unlike printkinit/trapinit neither needs the
   decoder's 4096-residue. *)
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
Require Import SpecInitlockWrapper.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to fileinit.                        *)
(* ===================================================================== *)

(* auipc a1,0x3 *)
Lemma fidb_00003597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00003597 : mword 32)) s
  = Some (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a1,a1,1468  -- a1 := &"ftable" *)
Lemma fidb_5bc58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5bc58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 1468 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* auipc a0,0x1e *)
Lemma fidb_0001e517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e517 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,1212  -- a0 := &ftable *)
Lemma fidb_4bc50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4bc50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initlock  (backwards: 2^21 - 13348) *)
Lemma fidb_bddfc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbddfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083804 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpFileinitDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FI := KernelSyms.fileinit.

  Lemma fii_00 : kernel_text -∗ instr (mword_of_int FI : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc FI (mword_of_int 0x1141 : mword 16)
    (mword_of_int FI : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_ccc exec_execute_C_ADDI. Qed.

  Lemma fii_02 : kernel_text -∗ instr (mword_of_int (FI + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FI + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (FI + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) mdec_cce exec_execute_C_SDSP. Qed.

  Lemma fii_04 : kernel_text -∗ instr (mword_of_int (FI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FI + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (FI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) mdec_cd0 exec_execute_C_SDSP. Qed.

  Lemma fii_06 : kernel_text -∗ instr (mword_of_int (FI + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FI + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (FI + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) mdec_cd2 exec_execute_C_ADDI4SPN. Qed.

  Lemma fii_08 : kernel_text -∗ instr (mword_of_int (FI + 0x08) : mword 64) false (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (FI + 0x08)%Z (mword_of_int 0x00003597 : mword 32)
    (mword_of_int (FI + 0x08) : mword 64) (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC)) fidb_00003597. Qed.

  Lemma fii_0c : kernel_text -∗ instr (mword_of_int (FI + 0x0c) : mword 64) false (ITYPE (mword_of_int 1468 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (FI + 0x0c)%Z (mword_of_int 0x5bc58593 : mword 32)
    (mword_of_int (FI + 0x0c) : mword 64) (ITYPE (mword_of_int 1468 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) fidb_5bc58593. Qed.

  Lemma fii_10 : kernel_text -∗ instr (mword_of_int (FI + 0x10) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FI + 0x10)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FI + 0x10) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) fidb_0001e517. Qed.

  Lemma fii_14 : kernel_text -∗ instr (mword_of_int (FI + 0x14) : mword 64) false (ITYPE (mword_of_int 1212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FI + 0x14)%Z (mword_of_int 0x4bc50513 : mword 32)
    (mword_of_int (FI + 0x14) : mword 64) (ITYPE (mword_of_int 1212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fidb_4bc50513. Qed.

  Lemma fii_18 : kernel_text -∗ instr (mword_of_int (FI + 0x18) : mword 64) false (JAL (mword_of_int 2083804 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FI + 0x18)%Z (mword_of_int 0xbddfc0ef : mword 32)
    (mword_of_int (FI + 0x18) : mword 64) (JAL (mword_of_int 2083804 : mword 21, Regidx (mword_of_int 1))) fidb_bddfc0ef. Qed.

  Lemma fii_1c : kernel_text -∗ instr (mword_of_int (FI + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FI + 0x1c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (FI + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) mdec_cea exec_execute_C_LDSP. Qed.

  Lemma fii_1e : kernel_text -∗ instr (mword_of_int (FI + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FI + 0x1e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (FI + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) mdec_cec exec_execute_C_LDSP. Qed.

  Lemma fii_20 : kernel_text -∗ instr (mword_of_int (FI + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FI + 0x20)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (FI + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) mdec_cee exec_execute_C_ADDI. Qed.

  Lemma fii_22 : kernel_text -∗ instr (mword_of_int (FI + 0x22) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FI + 0x22)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FI + 0x22) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* fileinit's thirteen instructions, in the thin-initlock-wrapper pattern.
     The five immediates are exactly what the whole-function proof needs to
     know about fileinit's code. *)
  Lemma fii_code :
    kernel_text -∗ ilw_code FI (mword_of_int 3) (mword_of_int 30)
                            (mword_of_int 1468) (mword_of_int 1212) (mword_of_int 2083804).
  Proof.
    iIntros "#Ht". rewrite /ilw_code.
    iSplitR; [iApply (fii_00 with "Ht")|].
    iSplitR; [iApply (fii_02 with "Ht")|].
    iSplitR; [iApply (fii_04 with "Ht")|].
    iSplitR; [iApply (fii_06 with "Ht")|].
    iSplitR; [iApply (fii_08 with "Ht")|].
    iSplitR; [iApply (fii_0c with "Ht")|].
    iSplitR; [iApply (fii_10 with "Ht")|].
    iSplitR; [iApply (fii_14 with "Ht")|].
    iSplitR; [iApply (fii_18 with "Ht")|].
    iSplitR; [iApply (fii_1c with "Ht")|].
    iSplitR; [iApply (fii_1e with "Ht")|].
    iSplitR; [iApply (fii_20 with "Ht")|].
    iApply (fii_22 with "Ht").
  Qed.

End WpFileinitDecode.

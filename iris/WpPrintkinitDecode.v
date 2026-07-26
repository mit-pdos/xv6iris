(* WpPrintkinitDecode.v -- the instruction-DECODE layer for xv6's printkinit().
   For every instruction of

     printkinit @ 0x80000862 .. 0x80000884   (offsets 0x00 .. 0x22)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pki_<off>]).
   printkinit uses the standard 16-byte frame, so every compressed word is one of
   the shared [cdec_*] templates from KernelRvcDecode, and the two auipc words it
   shares with kinit come from KernelBaseDecode; only the three base words that
   carry printkinit's own immediates (the two addi's and the jal to initlock) get
   fresh decode helpers here. *)
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
Require Import KernelRvcDecode KernelBaseDecode.
Require Import SpecInitlockWrapper.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to printkinit.                       *)
(* ===================================================================== *)

(* addi a1,a1,1982  -- a1 := &"pr" *)
Lemma fdb_7be58593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7be58593 : mword 32)) s
  = Some (ITYPE (mword_of_int 1982 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,-1402  -- a0 := &pr  (the decoder's positive residue: 4096-1402) *)
Lemma fdb_a8650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa8650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2694 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,initlock *)
Lemma fdb_30e000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x30e000ef : mword 32)) s
  = Some (JAL (mword_of_int 782 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Section WpPrintkinitDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PK := KernelSyms.printkinit.

  Lemma pki_00 : kernel_text -∗ instr (mword_of_int PK : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc PK (mword_of_int 0x1141 : mword 16)
    (mword_of_int PK : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma pki_02 : kernel_text -∗ instr (mword_of_int (PK + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PK + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (PK + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma pki_04 : kernel_text -∗ instr (mword_of_int (PK + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PK + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (PK + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma pki_06 : kernel_text -∗ instr (mword_of_int (PK + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PK + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (PK + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma pki_08 : kernel_text -∗ instr (mword_of_int (PK + 0x08) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (PK + 0x08)%Z (mword_of_int 0x00006597 : mword 32)
    (mword_of_int (PK + 0x08) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00006597. Qed.

  Lemma pki_0c : kernel_text -∗ instr (mword_of_int (PK + 0x0c) : mword 64) false (ITYPE (mword_of_int 1982 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PK + 0x0c)%Z (mword_of_int 0x7be58593 : mword 32)
    (mword_of_int (PK + 0x0c) : mword 64) (ITYPE (mword_of_int 1982 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) fdb_7be58593. Qed.

  Lemma pki_10 : kernel_text -∗ instr (mword_of_int (PK + 0x10) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (PK + 0x10)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (PK + 0x10) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma pki_14 : kernel_text -∗ instr (mword_of_int (PK + 0x14) : mword 64) false (ITYPE (mword_of_int 2694 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x14)%Z (mword_of_int 0xa8650513 : mword 32)
    (mword_of_int (PK + 0x14) : mword 64) (ITYPE (mword_of_int 2694 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fdb_a8650513. Qed.

  Lemma pki_18 : kernel_text -∗ instr (mword_of_int (PK + 0x18) : mword 64) false (JAL (mword_of_int 782 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x18)%Z (mword_of_int 0x30e000ef : mword 32)
    (mword_of_int (PK + 0x18) : mword 64) (JAL (mword_of_int 782 : mword 21, Regidx (mword_of_int 1))) fdb_30e000ef. Qed.

  Lemma pki_1c : kernel_text -∗ instr (mword_of_int (PK + 0x1c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PK + 0x1c)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (PK + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma pki_1e : kernel_text -∗ instr (mword_of_int (PK + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PK + 0x1e)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (PK + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma pki_20 : kernel_text -∗ instr (mword_of_int (PK + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PK + 0x20)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (PK + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma pki_22 : kernel_text -∗ instr (mword_of_int (PK + 0x22) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PK + 0x22)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PK + 0x22) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* printkinit's thirteen instructions, in the thin-initlock-wrapper pattern
     (SpecInitlockWrapper.v) that its whole-function proof instantiates. *)
  Lemma pki_code :
    kernel_text -∗ ilw_code PK (mword_of_int 6) (mword_of_int 18)
                            (mword_of_int 1982) (mword_of_int 2694) (mword_of_int 782).
  Proof.
    iIntros "#Ht". rewrite /ilw_code.
    iSplitR; [iApply (pki_00 with "Ht")|].
    iSplitR; [iApply (pki_02 with "Ht")|].
    iSplitR; [iApply (pki_04 with "Ht")|].
    iSplitR; [iApply (pki_06 with "Ht")|].
    iSplitR; [iApply (pki_08 with "Ht")|].
    iSplitR; [iApply (pki_0c with "Ht")|].
    iSplitR; [iApply (pki_10 with "Ht")|].
    iSplitR; [iApply (pki_14 with "Ht")|].
    iSplitR; [iApply (pki_18 with "Ht")|].
    iSplitR; [iApply (pki_1c with "Ht")|].
    iSplitR; [iApply (pki_1e with "Ht")|].
    iSplitR; [iApply (pki_20 with "Ht")|].
    iApply (pki_22 with "Ht").
  Qed.

End WpPrintkinitDecode.

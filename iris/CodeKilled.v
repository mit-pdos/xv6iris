(* CodeKilled.v -- the machine code of killed(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofKilled.v. *)



From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.


Notation kl_ra := (mword_of_int 1 : mword 5).

Section CodeKilled.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation KLI o t d := (kernel_text -∗ instr (mword_of_int (KernelSyms.killed + o) : mword 64) t d).


(* ---- the two decodes not already shared ---- *)
(* +0x12  0x549c  c.lw a5,40(s1)  -- p->killed *)
Lemma kldec_lw_killed s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x549c : mword 16)) s
  = Some (C_LW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* +0x0e  0xab9fe0ef  jal ra,acquire  (0x80002150 -> 0x80000c08 = -5448) *)
Lemma kldec_jal_acq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xab9fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2091704 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* +0x18  0xb37fe0ef  jal ra,release  (0x8000215a -> 0x80000c90 = -5322) *)
Lemma kldec_jal_rel s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb37fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2091830 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma kli_00 : KLI 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
Proof. mk_rvc (KernelSyms.killed + 0x00)%Z (mword_of_int 0x1101 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
Lemma kli_02 : KLI 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x02)%Z (mword_of_int 0xec06 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
Lemma kli_04 : KLI 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x04)%Z (mword_of_int 0xe822 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
Lemma kli_06 : KLI 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x06)%Z (mword_of_int 0xe426 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.
Lemma kli_08 : KLI 0x08 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x08)%Z (mword_of_int 0xe04a : mword 16)
  (mword_of_int (KernelSyms.killed + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.
Lemma kli_0a : KLI 0x0a true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
Proof. mk_rvc (KernelSyms.killed + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
Lemma kli_0c : KLI 0x0c true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
Proof. mk_rvc (KernelSyms.killed + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
  (mword_of_int (KernelSyms.killed + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
Lemma kli_0e : KLI 0x0e false (JAL (mword_of_int 2091704 : mword 21, Regidx kl_ra)).
Proof. mk_base (KernelSyms.killed + 0x0e)%Z (mword_of_int 0xab9fe0ef : mword 32)
  (mword_of_int (KernelSyms.killed + 0x0e) : mword 64) (JAL (mword_of_int 2091704 : mword 21, Regidx kl_ra)) kldec_jal_acq. Qed.
Lemma kli_12 : KLI 0x12 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
Proof. mk_rvc (KernelSyms.killed + 0x12)%Z (mword_of_int 0x549c : mword 16)
  (mword_of_int (KernelSyms.killed + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) kldec_lw_killed exec_execute_C_LW. Qed.
Lemma kli_14 : KLI 0x14 true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)).
Proof. mk_rvc (KernelSyms.killed + 0x14)%Z (mword_of_int 0x893e : mword 16)
  (mword_of_int (KernelSyms.killed + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)) cdec_893e exec_execute_C_MV. Qed.
Lemma kli_16 : KLI 0x16 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
Proof. mk_rvc (KernelSyms.killed + 0x16)%Z (mword_of_int 0x8526 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
Lemma kli_18 : KLI 0x18 false (JAL (mword_of_int 2091830 : mword 21, Regidx kl_ra)).
Proof. mk_base (KernelSyms.killed + 0x18)%Z (mword_of_int 0xb37fe0ef : mword 32)
  (mword_of_int (KernelSyms.killed + 0x18) : mword 64) (JAL (mword_of_int 2091830 : mword 21, Regidx kl_ra)) kldec_jal_rel. Qed.
Lemma kli_1c : KLI 0x1c true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
Proof. mk_rvc (KernelSyms.killed + 0x1c)%Z (mword_of_int 0x854a : mword 16)
  (mword_of_int (KernelSyms.killed + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.
Lemma kli_1e : KLI 0x1e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x1e)%Z (mword_of_int 0x60e2 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
Lemma kli_20 : KLI 0x20 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x20)%Z (mword_of_int 0x6442 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
Lemma kli_22 : KLI 0x22 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x22)%Z (mword_of_int 0x64a2 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.
Lemma kli_24 : KLI 0x24 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
Proof. mk_rvc (KernelSyms.killed + 0x24)%Z (mword_of_int 0x6902 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.
Lemma kli_26 : KLI 0x26 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
Proof. mk_rvc (KernelSyms.killed + 0x26)%Z (mword_of_int 0x6105 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x26) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
Lemma kli_28 : KLI 0x28 true (JALR (zeros' 12, Regidx kl_ra, zreg)).
Proof. mk_rvc (KernelSyms.killed + 0x28)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (KernelSyms.killed + 0x28) : mword 64) (JALR (zeros' 12, Regidx kl_ra, zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeKilled.

(* CodeSetkilled.v -- the machine code of setkilled(): the decode templates
   for the words this function alone uses, and the [instr] constructors for
   its instruction addresses.  Consumed by ProofSetkilled.v.

     +0x00  1101      c.addi     sp,sp,-32
     +0x02  ec06      c.sdsp     ra,24(sp)
     +0x04  e822      c.sdsp     s0,16(sp)
     +0x06  e426      c.sdsp     s1,8(sp)
     +0x08  1000      c.addi4spn s0,sp,32
     +0x0a  84aa      c.mv       s1,a0        park [p] across the two calls
     +0x0c  adffe0ef  jal        ra,acquire
     +0x10  4785      c.li       a5,1
     +0x12  d49c      c.sw       a5,40(s1)    p->killed = 1
     +0x14  8526      c.mv       a0,s1
     +0x16  b5dfe0ef  jal        ra,release
     +0x1a  60e2      c.ldsp     ra,24(sp)
     +0x1c  6442      c.ldsp     s0,16(sp)
     +0x1e  64a2      c.ldsp     s1,8(sp)
     +0x20  6105      c.addi16sp sp,32
     +0x22  8082      c.ret

   Slot 0 of the 32-byte frame is padding: setkilled saves three registers,
   not four (killed's fourth slot holds s2, the value it parks across
   release -- a void function has nothing to park). *)
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

Local Notation SK := KernelSyms.setkilled.

Notation sk_ra := (mword_of_int 1 : mword 5).

(* [cdec_d49c] / [cexec_d49c] -- the [c.sw a5,40(s1)] -- live in
   KernelRvcDecode.v: kkill stores the same word at the same offset. *)

Section CodeSetkilled.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation SKI o t d := (kernel_text -∗ instr (mword_of_int (SK + o) : mword 64) t d).

  (* +0x0c  0xadffe0ef  jal ra,acquire  (0x8000212a -> 0x80000c08 = -5410) *)
  Lemma skdec_jal_acq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xadffe0ef : mword 32)) s
    = Some (JAL (mword_of_int 2091742 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x16  0xb5dfe0ef  jal ra,release  (0x80002134 -> 0x80000c90 = -5284) *)
  Lemma skdec_jal_rel s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xb5dfe0ef : mword 32)) s
    = Some (JAL (mword_of_int 2091868 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.

  Lemma ski_00 : SKI 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (SK + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (SK + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
  Lemma ski_02 : SKI 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SK + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (SK + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
  Lemma ski_04 : SKI 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SK + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (SK + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
  Lemma ski_06 : SKI 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SK + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (SK + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.
  Lemma ski_08 : SKI 0x08 true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SK + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (SK + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
  Lemma ski_0a : SKI 0x0a true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (SK + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (SK + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.
  Lemma ski_0c : SKI 0x0c false (JAL (mword_of_int 2091742 : mword 21, Regidx sk_ra)).
  Proof. mk_base (SK + 0x0c)%Z (mword_of_int 0xadffe0ef : mword 32)
    (mword_of_int (SK + 0x0c) : mword 64) (JAL (mword_of_int 2091742 : mword 21, Regidx sk_ra)) skdec_jal_acq. Qed.
  Lemma ski_10 : SKI 0x10 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SK + 0x10)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (SK + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.
  Lemma ski_12 : SKI 0x12 true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (SK + 0x12)%Z (mword_of_int 0xd49c : mword 16)
    (mword_of_int (SK + 0x12) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_d49c cexec_d49c. Qed.
  Lemma ski_14 : SKI 0x14 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SK + 0x14)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SK + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma ski_16 : SKI 0x16 false (JAL (mword_of_int 2091868 : mword 21, Regidx sk_ra)).
  Proof. mk_base (SK + 0x16)%Z (mword_of_int 0xb5dfe0ef : mword 32)
    (mword_of_int (SK + 0x16) : mword 64) (JAL (mword_of_int 2091868 : mword 21, Regidx sk_ra)) skdec_jal_rel. Qed.
  Lemma ski_1a : SKI 0x1a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SK + 0x1a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (SK + 0x1a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
  Lemma ski_1c : SKI 0x1c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SK + 0x1c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (SK + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
  Lemma ski_1e : SKI 0x1e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SK + 0x1e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (SK + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.
  Lemma ski_20 : SKI 0x20 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SK + 0x20)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (SK + 0x20) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
  Lemma ski_22 : SKI 0x22 true (JALR (zeros' 12, Regidx sk_ra, zreg)).
  Proof. mk_rvc (SK + 0x22)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SK + 0x22) : mword 64) (JALR (zeros' 12, Regidx sk_ra, zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSetkilled.

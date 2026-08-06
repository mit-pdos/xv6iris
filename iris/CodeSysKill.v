(* CodeSysKill.v -- the machine code of sys_kill(): the decode templates for
   the words this function alone uses, and the [instr] constructors for its
   instruction addresses.  Consumed by ProofSysKill.v.

     +0x00  1101      c.addi     sp,sp,-32
     +0x02  ec06      c.sdsp     ra,24(sp)
     +0x04  e822      c.sdsp     s0,16(sp)
     +0x06  1000      c.addi4spn s0,sp,32
     +0x08  fec40593  addi       a1,s0,-20     a1 := &pid  (sp+12)
     +0x0c  4501      c.li       a0,0
     +0x0e  da5ff0ef  jal        ra,argint
     +0x12  fec42503  lw         a0,-20(s0)    a0 := pid
     +0x16  e50ff0ef  jal        ra,kkill
     +0x1a  60e2      c.ldsp     ra,24(sp)
     +0x1c  6442      c.ldsp     s0,16(sp)
     +0x1e  6105      c.addi16sp sp,sp,32
     +0x20  8082      c.ret

   [pid] is the UPPER half of frame slot 3 (sp+8..15), so the frame's
   [↦₈] view of that slot is split with [InstrBytes.word_pointsto_split4]
   and rejoined at the epilogue -- the shape sys_close's [fd] introduced. *)
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
Require Import KernelRvcDecode WpDecodeBridge.
From Kernel Require KernelInstrs KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Local Notation SKL := KernelSyms.sys_kill.

Notation skl_ra := (mword_of_int 1 : mword 5).

Section CodeSysKill.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation SKLI o t d := (kernel_text -∗ instr (mword_of_int (SKL + o) : mword 64) t d).

  (* +0x08  addi a1,s0,-20 *)
  Lemma skldec_addi_a1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfec40593 : mword 32)) s
    = Some (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x0e  jal ra,argint   (0x80002a60 -> 0x80002804 = -604) *)
  Lemma skldec_jal_argint s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xda5ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2096548 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x12  lw a0,-20(s0) *)
  Lemma skldec_lw_pid s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xfec42503 : mword 32)) s
    = Some (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4), s).
  Proof. decode_bridge_ms. Qed.
  (* +0x16  jal ra,kkill    (0x80002a68 -> 0x800020b8 = -2480) *)
  Lemma skldec_jal_kkill s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
    exec (ext_decode (mword_of_int 0xe50ff0ef : mword 32)) s
    = Some (JAL (mword_of_int 2094672 : mword 21, Regidx (mword_of_int 1)), s).
  Proof. decode_bridge_ms. Qed.

  Lemma skli_00 : SKLI 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (SKL + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (SKL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.
  Lemma skli_02 : SKLI 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SKL + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (SKL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.
  Lemma skli_04 : SKLI 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SKL + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (SKL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.
  Lemma skli_06 : SKLI 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SKL + 0x06)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (SKL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.
  Lemma skli_08 : SKLI 0x08 false (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SKL + 0x08)%Z (mword_of_int 0xfec40593 : mword 32)
    (mword_of_int (SKL + 0x08) : mword 64) (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) skldec_addi_a1. Qed.
  Lemma skli_0c : SKLI 0x0c true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SKL + 0x0c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SKL + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.
  Lemma skli_0e : SKLI 0x0e false (JAL (mword_of_int 2096548 : mword 21, Regidx skl_ra)).
  Proof. mk_base (SKL + 0x0e)%Z (mword_of_int 0xda5ff0ef : mword 32)
    (mword_of_int (SKL + 0x0e) : mword 64) (JAL (mword_of_int 2096548 : mword 21, Regidx skl_ra)) skldec_jal_argint. Qed.
  Lemma skli_12 : SKLI 0x12 false (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (SKL + 0x12)%Z (mword_of_int 0xfec42503 : mword 32)
    (mword_of_int (SKL + 0x12) : mword 64) (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 4)) skldec_lw_pid. Qed.
  Lemma skli_16 : SKLI 0x16 false (JAL (mword_of_int 2094672 : mword 21, Regidx skl_ra)).
  Proof. mk_base (SKL + 0x16)%Z (mword_of_int 0xe50ff0ef : mword 32)
    (mword_of_int (SKL + 0x16) : mword 64) (JAL (mword_of_int 2094672 : mword 21, Regidx skl_ra)) skldec_jal_kkill. Qed.
  Lemma skli_1a : SKLI 0x1a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SKL + 0x1a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (SKL + 0x1a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.
  Lemma skli_1c : SKLI 0x1c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SKL + 0x1c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (SKL + 0x1c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.
  Lemma skli_1e : SKLI 0x1e true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SKL + 0x1e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (SKL + 0x1e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.
  Lemma skli_20 : SKLI 0x20 true (JALR (zeros' 12, Regidx skl_ra, zreg)).
  Proof. mk_rvc (SKL + 0x20)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SKL + 0x20) : mword 64) (JALR (zeros' 12, Regidx skl_ra, zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSysKill.

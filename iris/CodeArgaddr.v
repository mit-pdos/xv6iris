(* CodeArgaddr.v -- the instruction-DECODE layer for xv6's argaddr().
   For EVERY instruction of

     argaddr @ 0x80002820 .. 0x8000283a   (offsets 0x00 .. 0x1a)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([aai_<off>]).

   argaddr's thirteen words are argint's thirteen with two changed: the jal's
   relocation (a different distance to argraw) and the store, which is a
   full-width [c.sd] here rather than argint's narrowing [c.sw].  Everything
   else -- the 32-byte ra/s0/s1 frame and the [c.mv s1,a1] that parks [ip]
   across the call -- comes out of KernelRvcDecode's shared base, so exactly
   ONE word ([0xeefff0ef]) is argaddr's alone.

     0x00 1101       c.addi     sp,sp,-32
     0x02 ec06       c.sdsp     ra,24(sp)
     0x04 e822       c.sdsp     s0,16(sp)
     0x06 e426       c.sdsp     s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84ae       c.mv       s1,a1            # s1 := ip (callee-saved)
     0x0c eefff0ef   jal        ra,argraw
     0x10 e088       c.sd       a0,0(s1)         # *ip = a0
     0x12 60e2       c.ldsp     ra,24(sp)
     0x14 6442       c.ldsp     s0,16(sp)
     0x16 64a2       c.ldsp     s1,8(sp)
     0x18 6105       c.addi16sp sp,32
     0x1a 8082       c.ret

   As in argint the frame's push is [c.addi sp,-32] while the pop is
   [c.addi16sp sp,32], so the two ends take different WP leaves. *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* The one word argaddr does not share with any other function.           *)
(* ===================================================================== *)

(* +0x0c  jal ra,argraw   (0x8000282c -> 0x8000271a is -274; the 21-bit
   field is 2^21 - 274 = 2096878) *)

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section ArgaddrInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma aai_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma aai_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma aai_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma aai_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma aai_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma aai_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x0a)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma aai_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) false (JAL (mword_of_int 2096878 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.argaddr + 0x0c)%Z (mword_of_int 0xeefff0ef : mword 32)
    (mword_of_int (KernelSyms.argaddr + 0x0c) : mword 64) (JAL (mword_of_int 2096878 : mword 21, Regidx (mword_of_int 1))) bdec_eefff0ef. Qed.

  (* the store's AST is already in leaf shape (a literal displacement and
     plain [Regidx]es) -- [cexec_sd0_s1_a0] does that normalisation. *)
  Lemma aai_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x10) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x10)%Z (mword_of_int 0xe088 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x10) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) cdec_e088 cexec_sd0_s1_a0. Qed.

  Lemma aai_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x12)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma aai_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x14)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma aai_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x16)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma aai_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x18) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x18)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x18) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma aai_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.argaddr + 0x1a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.argaddr + 0x1a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.argaddr + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End ArgaddrInstrs.

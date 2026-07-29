(* WpFetchaddrDecode.v -- the instruction-DECODE layer for xv6's fetchaddr().
   For EVERY instruction of

     fetchaddr @ 0x8000277a .. 0x800027c2   (offsets 0x00 .. 0x48)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fai_<off>]).

   The 32-byte frame is the ra/s0/s1/s2 set argfd and vmfault also use, so
   its ten words come from KernelRvcDecode's bit-keyed base -- as do the two
   [c.mv]s that park the arguments, [c.li a0,-1], both [c.j]s, [c.ld
   a5,72(a0)] (vmfault's [p->sz] load, same word) and [c.ret].  THREE
   compressed words are fetchaddr's alone ([c.li a3,8], [c.mv a2,s1] and
   [c.ld a0,80(a0)]), as are all seven base words.

     0x00 1101       c.addi     sp,sp,-32
     0x02 ec06       c.sdsp     ra,24(sp)
     0x04 e822       c.sdsp     s0,16(sp)
     0x06 e426       c.sdsp     s1,8(sp)
     0x08 e04a       c.sdsp     s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32          # s0 = entry sp
     0x0c 84aa       c.mv       s1,a0             # s1 := addr (callee-saved)
     0x0e 892e       c.mv       s2,a1             # s2 := ip   (callee-saved)
     0x10 97aff0ef   jal        ra,myproc
     0x14 653c       c.ld       a5,72(a0)         # a5 := p->sz
     0x16 02f4f663   bgeu       s1,a5,+0x2c       # addr >=u sz  -> -1
     0x1a 00848713   addi       a4,s1,8           # addr + 8
     0x1e 02e7e463   bltu       a5,a4,+0x28       # sz <u addr+8 -> -1
     0x22 46a1       c.li       a3,8              # len = sizeof(uint64)
     0x24 8626       c.mv       a2,s1             # srcva = addr
     0x26 85ca       c.mv       a1,s2             # dst   = ip
     0x28 6928       c.ld       a0,80(a0)         # a0 := p->pagetable
     0x2a f3ffe0ef   jal        ra,copyin
     0x2e 00a03533   snez       a0,a0             # = sltu a0,x0,a0
     0x32 40a0053b   negw       a0,a0             # = subw a0,x0,a0
     0x36 60e2       c.ldsp     ra,24(sp)         # <- ALL THREE arms join here
     0x38 6442       c.ldsp     s0,16(sp)
     0x3a 64a2       c.ldsp     s1,8(sp)
     0x3c 6902       c.ldsp     s2,0(sp)
     0x3e 6105       c.addi16sp sp,32
     0x40 8082       c.ret
     0x42 557d       c.li       a0,-1             # the bgeu arm
     0x44 bfcd       c.j        -0x0e             # -> +0x36
     0x46 557d       c.li       a0,-1             # the bltu arm
     0x48 b7fd       c.j        -0x12             # -> +0x36

   Note the ASYMMETRIC frame: the push is a plain [c.addi sp,-32] but the
   pop is [c.addi16sp sp,32], so the two take different WP leaves
   ([wp_caddi_sp_push_s_sconf] / [wp_caddi16sp_pop_s_sconf]).

   [snez]/[negw] are the pseudo-instructions that turn copyin's 0/-1 into
   fetchaddr's 0/-1 -- both read x0 as a SOURCE, which is why the proof needs
   [IntrDefs.sie_cap_gpr_x0] to compute the written value. *)
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
(* Compressed words fetchaddr does not share with any other function.     *)
(* ===================================================================== *)

(* +0x22  c.li a3,8 *)
Lemma fadc_46a1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x46a1 : mword 16)) s
  = Some (C_LI (mword_of_int 8, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x24  c.mv a2,s1 *)
Lemma fadc_8626 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8626 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_6928] -- shared, see KernelRvcDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x10  jal ra,myproc   (0x8000278a -> 0x80001904 is -3718) *)
Lemma fadb_97aff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x97aff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093434 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  bgeu s1,a5,+0x2c *)
Lemma fadb_02f4f663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f4f663 : mword 32)) s
  = Some (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* +0x1a  addi a4,s1,8 *)
Lemma fadb_00848713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00848713 : mword 32)) s
  = Some (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  bltu a5,a4,+0x28 *)
Lemma fadb_02e7e463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02e7e463 : mword 32)) s
  = Some (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* +0x2a  jal ra,copyin   (0x800027a4 -> 0x800016e2 is -4290) *)
Lemma fadb_f3ffe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf3ffe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092862 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x2e  snez a0,a0  =  sltu a0,x0,a0 *)
Lemma fadb_00a03533 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a03533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SLTU), s).
Proof. decode_bridge_ms. Qed.

(* +0x32  negw a0,a0  =  subw a0,x0,a0 *)
Lemma fadb_40a0053b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40a0053b : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FetchaddrInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FA := KernelSyms.fetchaddr.

  Lemma fai_00 : kernel_text -∗ instr (mword_of_int (FA + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FA + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (FA + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma fai_02 : kernel_text -∗ instr (mword_of_int (FA + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FA + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (FA + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma fai_04 : kernel_text -∗ instr (mword_of_int (FA + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FA + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (FA + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma fai_06 : kernel_text -∗ instr (mword_of_int (FA + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FA + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (FA + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma fai_08 : kernel_text -∗ instr (mword_of_int (FA + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (FA + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (FA + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma fai_0a : kernel_text -∗ instr (mword_of_int (FA + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FA + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (FA + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma fai_0c : kernel_text -∗ instr (mword_of_int (FA + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FA + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (FA + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma fai_0e : kernel_text -∗ instr (mword_of_int (FA + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (FA + 0x0e)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (FA + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma fai_10 : kernel_text -∗ instr (mword_of_int (FA + 0x10) : mword 64) false (JAL (mword_of_int 2093434 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FA + 0x10)%Z (mword_of_int 0x97aff0ef : mword 32)
    (mword_of_int (FA + 0x10) : mword 64) (JAL (mword_of_int 2093434 : mword 21, Regidx (mword_of_int 1))) fadb_97aff0ef. Qed.

  Lemma fai_14 : kernel_text -∗ instr (mword_of_int (FA + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (FA + 0x14)%Z (mword_of_int 0x653c : mword 16)
    (mword_of_int (FA + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) cdec_653c exec_execute_C_LD. Qed.

  Lemma fai_16 : kernel_text -∗ instr (mword_of_int (FA + 0x16) : mword 64) false (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BGEU)).
  Proof. mk_base (FA + 0x16)%Z (mword_of_int 0x02f4f663 : mword 32)
    (mword_of_int (FA + 0x16) : mword 64) (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BGEU)) fadb_02f4f663. Qed.

  Lemma fai_1a : kernel_text -∗ instr (mword_of_int (FA + 0x1a) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (FA + 0x1a)%Z (mword_of_int 0x00848713 : mword 32)
    (mword_of_int (FA + 0x1a) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), ADDI)) fadb_00848713. Qed.

  Lemma fai_1e : kernel_text -∗ instr (mword_of_int (FA + 0x1e) : mword 64) false (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (FA + 0x1e)%Z (mword_of_int 0x02e7e463 : mword 32)
    (mword_of_int (FA + 0x1e) : mword 64) (BTYPE (mword_of_int 40 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)) fadb_02e7e463. Qed.

  Lemma fai_22 : kernel_text -∗ instr (mword_of_int (FA + 0x22) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (FA + 0x22)%Z (mword_of_int 0x46a1 : mword 16)
    (mword_of_int (FA + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) fadc_46a1 exec_execute_C_LI. Qed.

  Lemma fai_24 : kernel_text -∗ instr (mword_of_int (FA + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (FA + 0x24)%Z (mword_of_int 0x8626 : mword 16)
    (mword_of_int (FA + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 12), ADD)) fadc_8626 exec_execute_C_MV. Qed.

  Lemma fai_26 : kernel_text -∗ instr (mword_of_int (FA + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (FA + 0x26)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (FA + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma fai_28 : kernel_text -∗ instr (mword_of_int (FA + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (FA + 0x28)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (FA + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma fai_2a : kernel_text -∗ instr (mword_of_int (FA + 0x2a) : mword 64) false (JAL (mword_of_int 2092862 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FA + 0x2a)%Z (mword_of_int 0xf3ffe0ef : mword 32)
    (mword_of_int (FA + 0x2a) : mword 64) (JAL (mword_of_int 2092862 : mword 21, Regidx (mword_of_int 1))) fadb_f3ffe0ef. Qed.

  Lemma fai_2e : kernel_text -∗ instr (mword_of_int (FA + 0x2e) : mword 64) false (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SLTU)).
  Proof. mk_base (FA + 0x2e)%Z (mword_of_int 0x00a03533 : mword 32)
    (mword_of_int (FA + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SLTU)) fadb_00a03533. Qed.

  Lemma fai_32 : kernel_text -∗ instr (mword_of_int (FA + 0x32) : mword 64) false (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)).
  Proof. mk_base (FA + 0x32)%Z (mword_of_int 0x40a0053b : mword 32)
    (mword_of_int (FA + 0x32) : mword 64) (RTYPEW (Regidx (mword_of_int 10), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)) fadb_40a0053b. Qed.

  Lemma fai_36 : kernel_text -∗ instr (mword_of_int (FA + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FA + 0x36)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (FA + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma fai_38 : kernel_text -∗ instr (mword_of_int (FA + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FA + 0x38)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (FA + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma fai_3a : kernel_text -∗ instr (mword_of_int (FA + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FA + 0x3a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (FA + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma fai_3c : kernel_text -∗ instr (mword_of_int (FA + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (FA + 0x3c)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (FA + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma fai_3e : kernel_text -∗ instr (mword_of_int (FA + 0x3e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FA + 0x3e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (FA + 0x3e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma fai_40 : kernel_text -∗ instr (mword_of_int (FA + 0x40) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FA + 0x40)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FA + 0x40) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma fai_42 : kernel_text -∗ instr (mword_of_int (FA + 0x42) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (FA + 0x42)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (FA + 0x42) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma fai_44 : kernel_text -∗ instr (mword_of_int (FA + 0x44) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FA + 0x44)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (FA + 0x44) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

  Lemma fai_46 : kernel_text -∗ instr (mword_of_int (FA + 0x46) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (FA + 0x46)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (FA + 0x46) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma fai_48 : kernel_text -∗ instr (mword_of_int (FA + 0x48) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FA + 0x48)%Z (mword_of_int 0xb7fd : mword 16)
    (mword_of_int (FA + 0x48) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)) cdec_b7fd exec_execute_C_J. Qed.

End FetchaddrInstrs.

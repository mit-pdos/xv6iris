(* WpFiledupDecode.v -- the instruction-DECODE layer for xv6's filedup().
   For EVERY instruction of

     filedup @ 0x80004016 .. 0x8000404e   (offsets 0x00 .. 0x38)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fdi_<off>]).
   Same shape as WpFileallocDecode; every compressed word filedup uses is
   already shared in KernelRvcDecode's bit-keyed base (the standard 32-byte
   frame, [c.mv], and -- because filealloc reads and writes the same [f->ref]
   field with the same registers -- [cdec_40dc]/[cdec_c0dc] and their
   leaf-form expansions), so nothing compressed is cloned here.

   The panic tail at +0x3a..+0x42 is deliberately ABSENT: the [blez] that
   jumps to it is proved to fall through (a caller holding a [file_ref] puts
   the slot in the authority's domain, so the count is positive), and a
   never-executed instruction needs no [instr] fact.

     0x00 1101       c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84aa       c.mv  s1,a0          # s1 := f
     0x0c 0001e517   auipc a0,0x1e
     0x10 43e50513   addi  a0,a0,1086     # a0 := &ftable
     0x14 bdffc0ef   jal   ra,acquire
     0x18 40dc       c.lw  a5,4(s1)       # a5 := f->ref
     0x1a 02f05063   bge   x0,a5,+0x20    # -> the panic tail; DEAD
     0x1e 2785       c.addiw a5,a5,1
     0x20 c0dc       c.sw  a5,4(s1)       # f->ref = a5
     0x22 0001e517   auipc a0,0x1e
     0x26 42850513   addi  a0,a0,1064     # a0 := &ftable
     0x2a c51fc0ef   jal   ra,release
     0x2e 8526       c.mv  a0,s1          # return f
     0x30 60e2       c.ldsp ra,24(sp)
     0x32 6442       c.ldsp s0,16(sp)
     0x34 64a2       c.ldsp s1,8(sp)
     0x36 6105       c.addi16sp sp,32
     0x38 8082       c.ret                                                    *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

Lemma fddb_43e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x43e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x43e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fddb_42850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x42850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fddb_bdffc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbdffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fcbde : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma fddb_c51fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc51fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fcc50 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* the [f->ref < 1] test: [bge x0,a5] -- rs1 is x0, so the branch is taken
   exactly when a5 is signed-nonpositive. *)
Lemma fddb_02f05063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f05063 : mword 32)) s
  = Some (BTYPE (mword_of_int 32 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FiledupInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FD := KernelSyms.filedup.

  Lemma fdi_00 : kernel_text -∗ instr (mword_of_int (FD + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FD + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (FD + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma fdi_02 : kernel_text -∗ instr (mword_of_int (FD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FD + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (FD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma fdi_04 : kernel_text -∗ instr (mword_of_int (FD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FD + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (FD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma fdi_06 : kernel_text -∗ instr (mword_of_int (FD + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FD + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (FD + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma fdi_08 : kernel_text -∗ instr (mword_of_int (FD + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FD + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (FD + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma fdi_0a : kernel_text -∗ instr (mword_of_int (FD + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FD + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (FD + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma fdi_0c : kernel_text -∗ instr (mword_of_int (FD + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FD + 0x0c)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FD + 0x0c) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fdi_10 : kernel_text -∗ instr (mword_of_int (FD + 0x10) : mword 64) false (ITYPE (mword_of_int 0x43e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FD + 0x10)%Z (mword_of_int 0x43e50513 : mword 32)
    (mword_of_int (FD + 0x10) : mword 64) (ITYPE (mword_of_int 0x43e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fddb_43e50513. Qed.

  Lemma fdi_14 : kernel_text -∗ instr (mword_of_int (FD + 0x14) : mword 64) false (JAL (mword_of_int 0x1fcbde : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FD + 0x14)%Z (mword_of_int 0xbdffc0ef : mword 32)
    (mword_of_int (FD + 0x14) : mword 64) (JAL (mword_of_int 0x1fcbde : mword 21, Regidx (mword_of_int 1))) fddb_bdffc0ef. Qed.

  Lemma fdi_18 : kernel_text -∗ instr (mword_of_int (FD + 0x18) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (FD + 0x18)%Z (mword_of_int 0x40dc : mword 16)
    (mword_of_int (FD + 0x18) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40dc cexec_40dc. Qed.

  Lemma fdi_1a : kernel_text -∗ instr (mword_of_int (FD + 0x1a) : mword 64) false (BTYPE (mword_of_int 32 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (FD + 0x1a)%Z (mword_of_int 0x02f05063 : mword 32)
    (mword_of_int (FD + 0x1a) : mword 64) (BTYPE (mword_of_int 32 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) fddb_02f05063. Qed.

  Lemma fdi_1e : kernel_text -∗ instr (mword_of_int (FD + 0x1e) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (FD + 0x1e)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (FD + 0x1e) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma fdi_20 : kernel_text -∗ instr (mword_of_int (FD + 0x20) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (FD + 0x20)%Z (mword_of_int 0xc0dc : mword 16)
    (mword_of_int (FD + 0x20) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0dc cexec_c0dc. Qed.

  Lemma fdi_22 : kernel_text -∗ instr (mword_of_int (FD + 0x22) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FD + 0x22)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FD + 0x22) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fdi_26 : kernel_text -∗ instr (mword_of_int (FD + 0x26) : mword 64) false (ITYPE (mword_of_int 0x428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FD + 0x26)%Z (mword_of_int 0x42850513 : mword 32)
    (mword_of_int (FD + 0x26) : mword 64) (ITYPE (mword_of_int 0x428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fddb_42850513. Qed.

  Lemma fdi_2a : kernel_text -∗ instr (mword_of_int (FD + 0x2a) : mword 64) false (JAL (mword_of_int 0x1fcc50 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FD + 0x2a)%Z (mword_of_int 0xc51fc0ef : mword 32)
    (mword_of_int (FD + 0x2a) : mword 64) (JAL (mword_of_int 0x1fcc50 : mword 21, Regidx (mword_of_int 1))) fddb_c51fc0ef. Qed.

  Lemma fdi_2e : kernel_text -∗ instr (mword_of_int (FD + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (FD + 0x2e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (FD + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma fdi_30 : kernel_text -∗ instr (mword_of_int (FD + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FD + 0x30)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (FD + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma fdi_32 : kernel_text -∗ instr (mword_of_int (FD + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FD + 0x32)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (FD + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma fdi_34 : kernel_text -∗ instr (mword_of_int (FD + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FD + 0x34)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (FD + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma fdi_36 : kernel_text -∗ instr (mword_of_int (FD + 0x36) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FD + 0x36)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (FD + 0x36) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma fdi_38 : kernel_text -∗ instr (mword_of_int (FD + 0x38) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FD + 0x38)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FD + 0x38) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End FiledupInstrs.

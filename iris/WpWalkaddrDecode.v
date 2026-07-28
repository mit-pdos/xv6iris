(* WpWalkaddrDecode.v -- the instruction-DECODE layer for xv6's walkaddr().

     walkaddr @ 0x80000ff6 .. 0x8000102f   (offsets 0x00 .. 0x38, 0x3a bytes)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([wai_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the five 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; walkaddr's own words are local, named [wadc_<word>]
   (compressed) / [wadb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/vm.c's walkaddr):

     0x00 57fd       c.li   a5,-1
     0x02 83e9       c.srli a5,a5,0x1a       # a5 := MAXVA-1 >> ... = 0x3fffffff
     0x04 00b7f463   bgeu   a5,a1,+0x08      # -> 0x0c, va < MAXVA: the real work
     0x08 4501       c.li   a0,0             # va >= MAXVA -> return 0
     0x0a 8082       c.ret
     0x0c 1141       c.addi sp,sp,-16        # 16-byte frame, ra/s0
     0x0e e406       c.sdsp ra,8(sp)
     0x10 e022       c.sdsp s0,0(sp)
     0x12 0800       c.addi4spn s0,sp,16
     0x14 4601       c.li   a2,0             # walk's alloc = 0
     0x16 f51ff0ef   jal    ra,walk          # -176
     0x1a c901       c.beqz a0,+0x10         # -> 0x2a, no pte -> return 0
     0x1c 611c       c.ld   a5,0(a0)         # a5 := *pte
     0x1e 0117f693   andi   a3,a5,17         # PTE_V|PTE_U
     0x22 4745       c.li   a4,17
     0x24 4501       c.li   a0,0             # the 0 return
     0x26 00e68663   beq    a3,a4,+0x0c      # -> 0x32, both bits set
     0x2a 60a2       c.ldsp ra,8(sp)         # <- the two long paths join here
     0x2c 6402       c.ldsp s0,0(sp)
     0x2e 0141       c.addi sp,sp,16
     0x30 8082       c.ret
     0x32 83a9       c.srli a5,a5,0xa        # PTE2PA: >> 10
     0x34 00c79513   slli   a0,a5,0xc        #         << 12
     0x38 bfcd       c.j    -0x0e            # -> 0x2a

   Note the two returns: the [va >= MAXVA] arm at 0x08 returns before the
   frame is even pushed and rets at 0x0a, while the three in-frame exits
   (no pte / not a user leaf / the physical address) all join the epilogue at
   0x2a -- 0x26 falls into it, 0x38 jumps back to it.

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.j] is 2041 (the 2^11 complement of -7 half-words) and the
   backward [jal] to walk is 2096976 (the 2^21 complement of -176 bytes,
   0x8000100c - 176 = 0x80000f5c).                                          *)
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
(* Compressed decode facts for walkaddr's own words.                      *)
(* ===================================================================== *)

(* 0x02  c.srli a5,a5,0x1a -- [cdec_83e9] (KernelRvcDecode.v) *)
(* 0x14  c.li a2,0        -- [cdec_4601] (KernelRvcDecode.v) *)

(* 0x1a  c.beqz a0,+0x10 *)
Lemma wadc_c901 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc901 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 8, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x22  c.li a4,17 *)
Lemma wadc_4745 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4745 : mword 16)) s
  = Some (C_LI (mword_of_int 17, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x32  c.srli a5,a5,0xa *)
Lemma wadc_83a9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x83a9 : mword 16)) s
  = Some (C_SRLI (mword_of_int 10, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all five are walkaddr's own.             *)
(* ===================================================================== *)

(* 0x04  bgeu a5,a1,+0x08  -- the [va < MAXVA] test (rs1 = a5, rs2 = a1) *)
Lemma wadb_00b7f463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b7f463 : mword 32)) s
  = Some (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x16  jal ra,walk       (0x8000100c -> 0x80000f5c is -176) *)
Lemma wadb_f51ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf51ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x1e  andi a3,a5,17     -- PTE_V|PTE_U *)
Lemma wadb_0117f693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0117f693 : mword 32)) s
  = Some (ITYPE (mword_of_int 17 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  beq a3,a4,+0x0c   -- both bits set? (rs1 = a3, rs2 = a4) *)
Lemma wadb_00e68663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e68663 : mword 32)) s
  = Some (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x34  slli a0,a5,0xc    -- the second half of PTE2PA *)
Lemma wadb_00c79513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c79513 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section WalkaddrInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation WA := KernelSyms.walkaddr.

  Local Notation WAP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (WA + off) : mword 64) rvc ast).

  (* --- the MAXVA test and the early 0-return ------------------------- *)

  Lemma wai_00 : WAP 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (WA + 0x00)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (WA + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma wai_02 : WAP 0x02 true (SHIFTIOP (mword_of_int 26 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (WA + 0x02)%Z (mword_of_int 0x83e9 : mword 16)
    (mword_of_int (WA + 0x02) : mword 64) (SHIFTIOP (mword_of_int 26 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83e9 exec_execute_C_SRLI. Qed.

  Lemma wai_04 : WAP 0x04 false (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU)).
  Proof. mk_base (WA + 0x04)%Z (mword_of_int 0x00b7f463 : mword 32)
    (mword_of_int (WA + 0x04) : mword 64) (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 15), BGEU)) wadb_00b7f463. Qed.

  Lemma wai_08 : WAP 0x08 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (WA + 0x08)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (WA + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma wai_0a : WAP 0x0a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (WA + 0x0a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (WA + 0x0a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- prologue: the 16-byte ra/s0 frame ----------------------------- *)

  Lemma wai_0c : WAP 0x0c true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (WA + 0x0c)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (WA + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma wai_0e : WAP 0x0e true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (WA + 0x0e)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (WA + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma wai_10 : WAP 0x10 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (WA + 0x10)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (WA + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma wai_12 : WAP 0x12 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (WA + 0x12)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (WA + 0x12) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* --- walk(pagetable, va, 0) and the pte test ----------------------- *)

  Lemma wai_14 : WAP 0x14 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (WA + 0x14)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (WA + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma wai_16 : WAP 0x16 false (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WA + 0x16)%Z (mword_of_int 0xf51ff0ef : mword 32)
    (mword_of_int (WA + 0x16) : mword 64) (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1))) wadb_f51ff0ef. Qed.

  Lemma wai_1a : WAP 0x1a true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (WA + 0x1a)%Z (mword_of_int 0xc901 : mword 16)
    (mword_of_int (WA + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) wadc_c901 exec_execute_C_BEQZ. Qed.

  Lemma wai_1c : WAP 0x1c true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (WA + 0x1c)%Z (mword_of_int 0x611c : mword 16)
    (mword_of_int (WA + 0x1c) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) cdec_611c cexec_611c. Qed.

  Lemma wai_1e : WAP 0x1e false (ITYPE (mword_of_int 17 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), ANDI)).
  Proof. mk_base (WA + 0x1e)%Z (mword_of_int 0x0117f693 : mword 32)
    (mword_of_int (WA + 0x1e) : mword 64) (ITYPE (mword_of_int 17 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), ANDI)) wadb_0117f693. Qed.

  Lemma wai_22 : WAP 0x22 true (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (WA + 0x22)%Z (mword_of_int 0x4745 : mword 16)
    (mword_of_int (WA + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 17 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) wadc_4745 exec_execute_C_LI. Qed.

  Lemma wai_24 : WAP 0x24 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (WA + 0x24)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (WA + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma wai_26 : WAP 0x26 false (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BEQ)).
  Proof. mk_base (WA + 0x26)%Z (mword_of_int 0x00e68663 : mword 32)
    (mword_of_int (WA + 0x26) : mword 64) (BTYPE (mword_of_int 12 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BEQ)) wadb_00e68663. Qed.

  (* --- the common epilogue, joined by all three in-frame exits -------- *)

  Lemma wai_2a : WAP 0x2a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (WA + 0x2a)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (WA + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma wai_2c : WAP 0x2c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (WA + 0x2c)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (WA + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma wai_2e : WAP 0x2e true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (WA + 0x2e)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (WA + 0x2e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma wai_30 : WAP 0x30 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (WA + 0x30)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (WA + 0x30) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- PTE2PA of the pte word, and the jump back to the epilogue ------ *)

  Lemma wai_32 : WAP 0x32 true (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (WA + 0x32)%Z (mword_of_int 0x83a9 : mword 16)
    (mword_of_int (WA + 0x32) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) wadc_83a9 exec_execute_C_SRLI. Qed.

  Lemma wai_34 : WAP 0x34 false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)).
  Proof. mk_base (WA + 0x34)%Z (mword_of_int 0x00c79513 : mword 32)
    (mword_of_int (WA + 0x34) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)) wadb_00c79513. Qed.

  Lemma wai_38 : WAP 0x38 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WA + 0x38)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (WA + 0x38) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

End WalkaddrInstrs.

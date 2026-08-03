(* CodeFetchstr.v -- the instruction-DECODE layer for xv6's fetchstr().

     fetchstr @ 0x800027c4 .. 0x80002803   (offsets 0x00 .. 0x3e, 64 bytes)

   One [kernel_text -* instr pc <is_rvc> <AST>] fact ([fsi_<off>]) per
   instruction plus the decode facts they consume.  Shared words come from
   KernelRvcDecode as [cdec_<word>]; fetchstr's own are [fsdc_]/[fsdb_].

   Straight-line with one branch: myproc, then copyinstr through
   [p->pagetable], then -- only if that returned >= 0 -- strlen over the
   buffer, and the two arms join at the 5-slot epilogue (+0x2e).  The
   [c.ld a0,80(a0)] at +0x1e is the same [p->pagetable] read fetchaddr does;
   [KernelRvcDecode.cshape_6928] is its shape in the form the leaf takes.   *)
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for this function's own words.                 *)
(* ===================================================================== *)


(* [cdec_86ca] -- shared, see KernelRvcDecode.v *)

(* [cdec_864e] -- shared, see KernelRvcDecode.v *)

(* [cdec_6928] -- shared, see KernelRvcDecode.v *)


(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* jal ra,myproc       # -3796 -> 0x80001904 *)
Lemma fsdb_92cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x92cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093356 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,copyinstr    # -4892 -> 0x800014c8 *)
Lemma fsdb_ce5fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xce5fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092260 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* bltz a0,+0x3c       # copyinstr failed -> return -1 *)
Lemma fsdb_00054c63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00054c63 : mword 32)) s
  = Some (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,strlen       # -6556 -> 0x80000e52 *)
Lemma fsdb_e64fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe64fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2090596 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InstrsFS.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma fsi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,-48   # 48-byte frame: ra/s0/s1/s2/s3 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma fsi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,40(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma fsi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,32(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma fsi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* c.sdsp s1,24(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma fsi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* c.sdsp s2,16(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma fsi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).  (* c.sdsp s3,8(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma fsi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,48 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma fsi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).  (* c.mv s3,a0          # s3 := addr *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x0e)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma fsi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,a1          # s1 := buf *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x10)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma fsi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 18), ADD)).  (* c.mv s2,a2          # s2 := max *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x12)%Z (mword_of_int 0x8932 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 18), ADD)) cdec_8932 exec_execute_C_MV. Qed.

  Lemma fsi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64) false (JAL (mword_of_int 2093356 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,myproc       # -3796 -> 0x80001904 *)
  Proof. mk_base (KernelSyms.fetchstr + 0x14)%Z (mword_of_int 0x92cff0ef : mword 32)
    (mword_of_int (KernelSyms.fetchstr + 0x14) : mword 64) (JAL (mword_of_int 2093356 : mword 21, Regidx (mword_of_int 1))) fsdb_92cff0ef. Qed.

  Lemma fsi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).  (* c.mv a3,s2 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x18)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) cdec_86ca exec_execute_C_MV. Qed.

  Lemma fsi_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)).  (* c.mv a2,s3 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x1a)%Z (mword_of_int 0x864e : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)) cdec_864e exec_execute_C_MV. Qed.

  Lemma fsi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s1 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x1c)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma fsi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).  (* c.ld a0,80(a0)      # a0 := p->pagetable *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x1e)%Z (mword_of_int 0x6928 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_6928 exec_execute_C_LD. Qed.

  Lemma fsi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64) false (JAL (mword_of_int 2092260 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,copyinstr    # -4892 -> 0x800014c8 *)
  Proof. mk_base (KernelSyms.fetchstr + 0x20)%Z (mword_of_int 0xce5fe0ef : mword 32)
    (mword_of_int (KernelSyms.fetchstr + 0x20) : mword 64) (JAL (mword_of_int 2092260 : mword 21, Regidx (mword_of_int 1))) fsdb_ce5fe0ef. Qed.

  Lemma fsi_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x24) : mword 64) false (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).  (* bltz a0,+0x3c       # copyinstr failed -> return -1 *)
  Proof. mk_base (KernelSyms.fetchstr + 0x24)%Z (mword_of_int 0x00054c63 : mword 32)
    (mword_of_int (KernelSyms.fetchstr + 0x24) : mword 64) (BTYPE (mword_of_int 24 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) fsdb_00054c63. Qed.

  Lemma fsi_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s1          # a0 := buf *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x28)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma fsi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64) false (JAL (mword_of_int 2090596 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,strlen       # -6556 -> 0x80000e52 *)
  Proof. mk_base (KernelSyms.fetchstr + 0x2a)%Z (mword_of_int 0xe64fe0ef : mword 32)
    (mword_of_int (KernelSyms.fetchstr + 0x2a) : mword 64) (JAL (mword_of_int 2090596 : mword 21, Regidx (mword_of_int 1))) fsdb_e64fe0ef. Qed.

  Lemma fsi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,40(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x2e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma fsi_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x30) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,32(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x30)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x30) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma fsi_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x32) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* c.ldsp s1,24(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x32)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x32) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma fsi_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* c.ldsp s2,16(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x34)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma fsi_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).  (* c.ldsp s3,8(sp) *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x36)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma fsi_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x38) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,48 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x38)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x38) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma fsi_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x3a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x3a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x3a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma fsi_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x3c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,-1 *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x3c)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x3c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma fsi_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.fetchstr + 0x3e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")), zreg)).  (* c.j -0x0c           # -> +0x2e, the epilogue *)
  Proof. mk_rvc (KernelSyms.fetchstr + 0x3e)%Z (mword_of_int 0xbfc5 : mword 16)
    (mword_of_int (KernelSyms.fetchstr + 0x3e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2040 : mword 11) ('b"0")), zreg)) cdec_bfc5 exec_execute_C_J. Qed.

End InstrsFS.

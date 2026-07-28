(* WpPrintkDecode.v -- the instruction-DECODE layer for xv6's printk().
   For every instruction of

     printk @ 0x800004fc .. 0x80000824   (offsets 0x00 .. 0x328)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pki_<off>]) plus
   the per-instruction decode facts they consume ([pkdc_<word>] compressed /
   [pkdb_<word>] base).  Generated mechanically from the image and checked by
   the kernel, as every other decode file is -- printk is 264 instructions and
   the dispatch chain alone accounts for a third of them. *)
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ---- per-word decode facts ---- *)

(* 0x00007a17  auipc s4,0x7 *)
Lemma pkdb_00007a17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00007a17 : mword 32)) s
  = Some (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x00007c97  auipc s9,0x7 *)
Lemma pkdb_00007c97 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00007c97 : mword 32)) s
  = Some (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 25), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x0000a797  auipc a5,0xa *)
Lemma pkdb_0000a797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0000a797 : mword 32)) s
  = Some (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x0004c503  lbu a0,0(s1) *)
Lemma pkdb_0004c503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004c503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x00074a83  lbu s5,0(a4) *)
Lemma pkdb_00074a83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00074a83 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 21), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x0007ba03  ld s4,0(a5) *)
Lemma pkdb_0007ba03 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007ba03 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 20), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x0007ba83  ld s5,0(a5) *)
Lemma pkdb_0007ba83 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007ba83 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 21), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x0007c503  lbu a0,0(a5) *)
Lemma pkdb_0007c503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007c503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x0007e503  lwu a0,0(a5) *)
Lemma pkdb_0007e503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007e503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x00094503  lbu a0,0(s2) *)
Lemma pkdb_00094503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00094503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x000a0d63  beqz s4,80000734 *)
Lemma pkdb_000a0d63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000a0d63 : mword 32)) s
  = Some (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x000a4503  lbu a0,0(s4) *)
Lemma pkdb_000a4503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000a4503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x00173713  seqz a4,a4 *)
Lemma pkdb_00173713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00173713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU), s).
Proof. decode_bridge_ms. Qed.

(* 0x00174683  lbu a3,1(a4) *)
Lemma pkdb_00174683 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00174683 : mword 32)) s
  = Some (LOAD (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x0017b793  seqz a5,a5 *)
Lemma pkdb_0017b793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017b793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTIU), s).
Proof. decode_bridge_ms. Qed.

(* 0x001a079b  addiw a5,s4,1 *)
Lemma pkdb_001a079b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x001a079b : mword 32)) s
  = Some (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0027c683  lbu a3,2(a5) *)
Lemma pkdb_0027c683 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0027c683 : mword 32)) s
  = Some (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x002a049b  addiw s1,s4,2 *)
Lemma pkdb_002a049b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x002a049b : mword 32)) s
  = Some (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9)), s).
Proof. decode_bridge_ms. Qed.

(* 0x003a049b  addiw s1,s4,3 *)
Lemma pkdb_003a049b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x003a049b : mword 32)) s
  = Some (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9)), s).
Proof. decode_bridge_ms. Qed.

(* 0x00840793  addi a5,s0,8 *)
Lemma pkdb_00840793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00840793 : mword 32)) s
  = Some (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x00878713  addi a4,a5,8 *)
Lemma pkdb_00878713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00878713 : mword 32)) s
  = Some (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x00f90733  add a4,s2,a5 *)
Lemma pkdb_00f90733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f90733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 14), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x0100  addi s0,sp,128 *)
Lemma pkdc_0100 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0100 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 32), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x02500513  li a0,37 *)
Lemma pkdb_02500513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02500513 : mword 32)) s
  = Some (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x02500793  li a5,37 *)
Lemma pkdb_02500793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02500793 : mword 32)) s
  = Some (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x02500993  li s3,37 *)
Lemma pkdb_02500993 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02500993 : mword 32)) s
  = Some (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 19), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x02800513  li a0,40 *)
Lemma pkdb_02800513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02800513 : mword 32)) s
  = Some (ITYPE (mword_of_int 40 : mword 12, zreg, Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x03000513  li a0,48 *)
Lemma pkdb_03000513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03000513 : mword 32)) s
  = Some (ITYPE (mword_of_int 48 : mword 12, zreg, Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x03043823  sd a6,48(s0) *)
Lemma pkdb_03043823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03043823 : mword 32)) s
  = Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 8), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x03143c23  sd a7,56(s0) *)
Lemma pkdb_03143c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03143c23 : mword 32)) s
  = Some (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 8), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x037a8863  beq s5,s7,800005d0 *)
Lemma pkdb_037a8863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x037a8863 : mword 32)) s
  = Some (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x03cad793  srli a5,s5,0x3c *)
Lemma pkdb_03cad793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03cad793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 60 : mword 6, Regidx (mword_of_int 21), Regidx (mword_of_int 15), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x03cc8c93  addi s9,s9,60 *)
Lemma pkdb_03cc8c93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03cc8c93 : mword 32)) s
  = Some (ITYPE (mword_of_int 60 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 25), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x06300793  li a5,99 *)
Lemma pkdb_06300793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06300793 : mword 32)) s
  = Some (ITYPE (mword_of_int 99 : mword 12, zreg, Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x06400b93  li s7,100 *)
Lemma pkdb_06400b93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06400b93 : mword 32)) s
  = Some (ITYPE (mword_of_int 100 : mword 12, zreg, Regidx (mword_of_int 23), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x07000d93  li s11,112 *)
Lemma pkdb_07000d93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07000d93 : mword 32)) s
  = Some (ITYPE (mword_of_int 112 : mword 12, zreg, Regidx (mword_of_int 27), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x07300793  li a5,115 *)
Lemma pkdb_07300793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07300793 : mword 32)) s
  = Some (ITYPE (mword_of_int 115 : mword 12, zreg, Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x07500c13  li s8,117 *)
Lemma pkdb_07500c13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07500c13 : mword 32)) s
  = Some (ITYPE (mword_of_int 117 : mword 12, zreg, Regidx (mword_of_int 24), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x07800513  li a0,120 *)
Lemma pkdb_07800513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07800513 : mword 32)) s
  = Some (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x07800d13  li s10,120 *)
Lemma pkdb_07800d13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07800d13 : mword 32)) s
  = Some (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 26), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x0a05  addi s4,s4,1 *)
Lemma pkdc_0a05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0a05 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0a92  slli s5,s5,0x4 *)
Lemma pkdc_0a92 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0a92 : mword 16)) s
  = Some (C_SLLI (mword_of_int 4, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1c050663  beqz a0,8000074a *)
Lemma pkdb_1c050663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1c050663 : mword 32)) s
  = Some (BTYPE (mword_of_int 460 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x1e068c63  beqz a3,80000794 *)
Lemma pkdb_1e068c63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1e068c63 : mword 32)) s
  = Some (BTYPE (mword_of_int 504 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 13), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x200a8963  beqz s5,800007a6 *)
Lemma pkdb_200a8963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x200a8963 : mword 32)) s
  = Some (BTYPE (mword_of_int 530 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x22050663  beqz a0,8000075c *)
Lemma pkdb_22050663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x22050663 : mword 32)) s
  = Some (BTYPE (mword_of_int 556 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x2485  addiw s1,s1,1 *)
Lemma pkdc_2485 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2485 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x3a7d  addiw s4,s4,-1 *)
Lemma pkdc_3a7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x3a7d : mword 16)) s
  = Some (C_ADDIW (mword_of_int 63, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4388  lw a0,0(a5) *)
Lemma pkdc_4388 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4388 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x45a9  li a1,10 *)
Lemma pkdc_45a9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x45a9 : mword 16)) s
  = Some (C_LI (mword_of_int 10, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x45c1  li a1,16 *)
Lemma pkdc_45c1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x45c1 : mword 16)) s
  = Some (C_LI (mword_of_int 16, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x4605  li a2,1 *)
Lemma pkdc_4605 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4605 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4a01  li s4,0 *)
Lemma pkdc_4a01 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4a01 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4a41  li s4,16 *)
Lemma pkdc_4a41 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4a41 : mword 16)) s
  = Some (C_LI (mword_of_int 16, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4b29  li s6,10 *)
Lemma pkdc_4b29 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4b29 : mword 16)) s
  = Some (C_LI (mword_of_int 10, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x502000ef  jal 80000c90 *)
Lemma pkdb_502000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x502000ef : mword 32)) s
  = Some (JAL (mword_of_int 1282 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x6129  addi sp,sp,192 *)
Lemma pkdc_6129 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6129 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 12 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6388  ld a0,0(a5) *)
Lemma pkdc_6388 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6388 : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 7), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x69e6  ld s3,88(sp) *)
Lemma pkdc_69e6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69e6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6a0000ef  jal 80000c08 *)
Lemma pkdb_6a0000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6a0000ef : mword 32)) s
  = Some (JAL (mword_of_int 1696 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x6a46  ld s4,80(sp) *)
Lemma pkdc_6a46 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a46 : mword 16)) s
  = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6aa6  ld s5,72(sp) *)
Lemma pkdc_6aa6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6aa6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6b06  ld s6,64(sp) *)
Lemma pkdc_6b06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6b06 : mword 16)) s
  = Some (C_LDSP (mword_of_int 8, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6de2  ld s11,24(sp) *)
Lemma pkdc_6de2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6de2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70e6  ld ra,120(sp) *)
Lemma pkdc_70e6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70e6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 15, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7131  addi sp,sp,-192 *)
Lemma pkdc_7131 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7131 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 52 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7446  ld s0,112(sp) *)
Lemma pkdc_7446 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7446 : mword 16)) s
  = Some (C_LDSP (mword_of_int 14, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x74a6  ld s1,104(sp) *)
Lemma pkdc_74a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x74a6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7906  ld s2,96(sp) *)
Lemma pkdc_7906 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7906 : mword 16)) s
  = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7be2  ld s7,56(sp) *)
Lemma pkdc_7be2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7be2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7c42  ld s8,48(sp) *)
Lemma pkdc_7c42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7c42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7ca2  ld s9,40(sp) *)
Lemma pkdc_7ca2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ca2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7d02  ld s10,32(sp) *)
Lemma pkdc_7d02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7d02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x84d2  mv s1,s4 *)
Lemma pkdc_84d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84d2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8556  mv a0,s5 *)
Lemma pkdc_8556 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8556 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x8636  mv a2,a3 *)
Lemma pkdc_8636 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8636 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8656  mv a2,s5 *)
Lemma pkdc_8656 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8656 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x86d6  mv a3,s5 *)
Lemma pkdc_86d6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86d6 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x892a  mv s2,a0 *)
Lemma pkdc_892a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x892a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8a26  mv s4,s1 *)
Lemma pkdc_8a26 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8a26 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8d4a0a13  addi s4,s4,-1836 *)
Lemma pkdb_8d4a0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8d4a0a13 : mword 32)) s
  = Some (ITYPE (mword_of_int 2260 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x8ff9  and a5,a5,a4 *)
Lemma pkdc_8ff9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8ff9 : mword 16)) s
  = Some (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x94ca  add s1,s1,s2 *)
Lemma pkdc_94ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94ca : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97ca  add a5,a5,s2 *)
Lemma pkdc_97ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ca : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x97e6  add a5,a5,s9 *)
Lemma pkdc_97e6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97e6 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa00d  j 800007c6 *)
Lemma pkdc_a00d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa00d : mword 16)) s
  = Some (C_J (mword_of_int 17 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa015  j 80000582 *)
Lemma pkdc_a015 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa015 : mword 16)) s
  = Some (C_J (mword_of_int 18 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa2c9  j 800007b2 *)
Lemma pkdc_a2c9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa2c9 : mword 16)) s
  = Some (C_J (mword_of_int 225 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa5dff0ef  jal 8000027c *)
Lemma pkdb_a5dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa5dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095708 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xa63ff0ef  jal 8000027c *)
Lemma pkdb_a63ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa63ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095714 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xac87a783  lw a5,-1336(a5) *)
Lemma pkdb_ac87a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xac87a783 : mword 32)) s
  = Some (LOAD (mword_of_int 2760 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xb39ff0ef  jal 8000027c *)
Lemma pkdb_b39ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb39ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095928 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xb535  j 80000574 *)
Lemma pkdc_b535 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb535 : mword 16)) s
  = Some (C_J (mword_of_int 1814 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb541  j 80000574 *)
Lemma pkdc_b541 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb541 : mword 16)) s
  = Some (C_J (mword_of_int 1856 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb57ff0ef  jal 8000027c *)
Lemma pkdb_b57ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb57ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095958 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xb589  j 80000574 *)
Lemma pkdc_b589 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb589 : mword 16)) s
  = Some (C_J (mword_of_int 1825 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb5b5  j 80000574 *)
Lemma pkdc_b5b5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb5b5 : mword 16)) s
  = Some (C_J (mword_of_int 1846 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb5cd  j 80000574 *)
Lemma pkdc_b5cd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb5cd : mword 16)) s
  = Some (C_J (mword_of_int 1905 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb5d9  j 80000574 *)
Lemma pkdc_b5d9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb5d9 : mword 16)) s
  = Some (C_J (mword_of_int 1891 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7250513  addi a0,a0,-1166 *)
Lemma pkdb_b7250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb7250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2930 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xb75d  j 80000574 *)
Lemma pkdc_b75d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb75d : mword 16)) s
  = Some (C_J (mword_of_int 2003 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb779  j 80000574 *)
Lemma pkdc_b779 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb779 : mword 16)) s
  = Some (C_J (mword_of_int 1991 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb79ff0ef  jal 8000027c *)
Lemma pkdb_b79ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb79ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095992 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xb7a5  j 80000574 *)
Lemma pkdc_b7a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7a5 : mword 16)) s
  = Some (C_J (mword_of_int 1972 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7b9  j 80000574 *)
Lemma pkdc_b7b9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7b9 : mword 16)) s
  = Some (C_J (mword_of_int 1959 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb7dd  j 80000726 *)
Lemma pkdc_b7dd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7dd : mword 16)) s
  = Some (C_J (mword_of_int 2035 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb97ff0ef  jal 8000027c *)
Lemma pkdb_b97ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb97ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096022 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xbafff0ef  jal 8000027c *)
Lemma pkdb_bafff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbafff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096046 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xbb7ff0ef  jal 8000027c *)
Lemma pkdb_bb7ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbb7ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096054 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xbb81  j 80000574 *)
Lemma pkdc_bb81 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbb81 : mword 16)) s
  = Some (C_J (mword_of_int 1704 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbdf5  j 80000574 *)
Lemma pkdc_bdf5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbdf5 : mword 16)) s
  = Some (C_J (mword_of_int 1918 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbf0d  j 80000574 *)
Lemma pkdc_bf0d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf0d : mword 16)) s
  = Some (C_J (mword_of_int 1945 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbf19  j 80000574 *)
Lemma pkdc_bf19 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf19 : mword 16)) s
  = Some (C_J (mword_of_int 1931 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbf65  j 80000524 *)
Lemma pkdc_bf65 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf65 : mword 16)) s
  = Some (C_J (mword_of_int 2012 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbfd1  j 80000766 *)
Lemma pkdc_bfd1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfd1 : mword 16)) s
  = Some (C_J (mword_of_int 2026 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbfe1  j 8000075c *)
Lemma pkdc_bfe1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfe1 : mword 16)) s
  = Some (C_J (mword_of_int 2028 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc38d  beqz a5,80000786 *)
Lemma pkdc_c38d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc38d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 17, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcb1d  beqz a4,800005e8 *)
Lemma pkdc_cb1d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb1d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 27, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcf9d  beqz a5,80000560 *)
Lemma pkdc_cf9d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf9d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 31, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd0a7a783  lw a5,-758(a5) *)
Lemma pkdb_d0a7a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd0a7a783 : mword 32)) s
  = Some (LOAD (mword_of_int 3338 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xd0fff0ef  jal 8000027c *)
Lemma pkdb_d0fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd0fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096398 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xd9850513  addi a0,a0,-616 *)
Lemma pkdb_d9850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd9850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3480 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xdc1ff0ef  jal 80000466 *)
Lemma pkdb_dc1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdc1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096576 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xdddff0ef  jal 80000466 *)
Lemma pkdb_dddff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdddff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096604 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xdf3ff0ef  jal 80000466 *)
Lemma pkdb_df3ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdf3ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096626 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe0da  sd s6,64(sp) *)
Lemma pkdc_e0da s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe0da : mword 16)) s
  = Some (C_SDSP (mword_of_int 8, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe11ff0ef  jal 80000466 *)
Lemma pkdb_e11ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe11ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096656 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe199  bnez a1,800007c6 *)
Lemma pkdc_e199 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe199 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe20798e3  bnez a5,800005f2 *)
Lemma pkdb_e20798e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe20798e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7728 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xe219  bnez a2,800007ec *)
Lemma pkdc_e219 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe219 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe299  bnez a3,800007f6 *)
Lemma pkdc_e299 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe299 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 3, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe2dff0ef  jal 80000466 *)
Lemma pkdb_e2dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe2dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096684 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe37a8ee3  beq s5,s7,800005d0 *)
Lemma pkdb_e37a8ee3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe37a8ee3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7740 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xe40509e3  beqz a0,80000574 *)
Lemma pkdb_e40509e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe40509e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7762 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xe4071ce3  bnez a4,80000628 *)
Lemma pkdb_e4071ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe4071ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7768 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xe40c  sd a1,8(s0) *)
Lemma pkdc_e40c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe40c : mword 16)) s
  = Some (C_SD (mword_of_int 1, Cregidx (mword_of_int 0), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe45ff0ef  jal 80000466 *)
Lemma pkdb_e45ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe45ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096708 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe4d6  sd s5,72(sp) *)
Lemma pkdc_e4d6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe4d6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe58a84e3  beq s5,s8,8000060e *)
Lemma pkdb_e58a84e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe58a84e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7752 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xe60795e3  bnez a5,80000644 *)
Lemma pkdb_e60795e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe60795e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7786 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xe63ff0ef  jal 80000466 *)
Lemma pkdb_e63ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe63ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096738 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe80719e3  bnez a4,8000067a *)
Lemma pkdb_e80719e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe80719e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7826 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xe810  sd a2,16(s0) *)
Lemma pkdc_e810 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe810 : mword 16)) s
  = Some (C_SD (mword_of_int 2, Cregidx (mword_of_int 0), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe85ff0ef  jal 80000466 *)
Lemma pkdb_e85ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe85ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096772 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe8d2  sd s4,80(sp) *)
Lemma pkdc_e8d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8d2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 10, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe9aa81e3  beq s5,s10,80000660 *)
Lemma pkdb_e9aa81e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe9aa81e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7810 : mword 13, Regidx (mword_of_int 26), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xea0791e3  bnez a5,80000694 *)
Lemma pkdb_ea0791e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xea0791e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7842 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xea1ff0ef  jal 80000466 *)
Lemma pkdb_ea1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xea1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096800 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xebba8de3  beq s5,s11,800006b0 *)
Lemma pkdb_ebba8de3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xebba8de3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7866 : mword 13, Regidx (mword_of_int 27), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xec14  sd a3,24(s0) *)
Lemma pkdc_ec14 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec14 : mword 16)) s
  = Some (C_SD (mword_of_int 3, Cregidx (mword_of_int 0), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec6e  sd s11,24(sp) *)
Lemma pkdc_ec6e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec6e : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xecce  sd s3,88(sp) *)
Lemma pkdc_ecce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xecce : mword 16)) s
  = Some (C_SDSP (mword_of_int 11, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xee05  bnez a2,800005e8 *)
Lemma pkdc_ee05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xee05 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 28, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xeefa8ce3  beq s5,a5,800006f6 *)
Lemma pkdb_eefa8ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeefa8ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7928 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xf018  sd a4,32(s0) *)
Lemma pkdc_f018 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf018 : mword 16)) s
  = Some (C_SD (mword_of_int 4, Cregidx (mword_of_int 0), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf06a  sd s10,32(sp) *)
Lemma pkdc_f06a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf06a : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf0ca  sd s2,96(sp) *)
Lemma pkdc_f0ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0ca : mword 16)) s
  = Some (C_SDSP (mword_of_int 12, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf0fa82e3  beq s5,a5,8000070a *)
Lemma pkdb_f0fa82e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf0fa82e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7940 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xf2fa8ae3  beq s5,a5,80000742 *)
Lemma pkdb_f2fa8ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf2fa8ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 7988 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xf41c  sd a5,40(s0) *)
Lemma pkdc_f41c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf41c : mword 16)) s
  = Some (C_SD (mword_of_int 5, Cregidx (mword_of_int 0), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf466  sd s9,40(sp) *)
Lemma pkdc_f466 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf466 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf4a6  sd s1,104(sp) *)
Lemma pkdc_f4a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf4a6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 13, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf60a80e3  beqz s5,80000772 *)
Lemma pkdb_f60a80e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf60a80e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8032 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xf862  sd s8,48(sp) *)
Lemma pkdc_f862 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf862 : mword 16)) s
  = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf8843783  ld a5,-120(s0) *)
Lemma pkdb_f8843783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8843783 : mword 32)) s
  = Some (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8860613  addi a2,a2,-120 *)
Lemma pkdb_f8860613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8860613 : mword 32)) s
  = Some (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8868693  addi a3,a3,-120 *)
Lemma pkdb_f8868693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8868693 : mword 32)) s
  = Some (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8a2  sd s0,112(sp) *)
Lemma pkdc_f8a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf8a2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 14, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf8b60593  addi a1,a2,-117 *)
Lemma pkdb_f8b60593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8b60593 : mword 32)) s
  = Some (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8b68593  addi a1,a3,-117 *)
Lemma pkdb_f8b68593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8b68593 : mword 32)) s
  = Some (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8e43423  sd a4,-120(s0) *)
Lemma pkdb_f8e43423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8e43423 : mword 32)) s
  = Some (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8f43423  sd a5,-120(s0) *)
Lemma pkdb_f8f43423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8f43423 : mword 32)) s
  = Some (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0xf9460793  addi a5,a2,-108 *)
Lemma pkdb_f9460793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9460793 : mword 32)) s
  = Some (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf94a8713  addi a4,s5,-108 *)
Lemma pkdb_f94a8713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf94a8713 : mword 32)) s
  = Some (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf97d  bnez a0,80000726 *)
Lemma pkdc_f97d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf97d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 251, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf9c68593  addi a1,a3,-100 *)
Lemma pkdb_f9c68593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9c68593 : mword 32)) s
  = Some (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf9c68613  addi a2,a3,-100 *)
Lemma pkdb_f9c68613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9c68613 : mword 32)) s
  = Some (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfc5e  sd s7,56(sp) *)
Lemma pkdc_fc5e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc5e : mword 16)) s
  = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfc86  sd ra,120(sp) *)
Lemma pkdc_fc86 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc86 : mword 16)) s
  = Some (C_SDSP (mword_of_int 15, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfe0a17e3  bnez s4,800006dc *)
Lemma pkdb_fe0a17e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe0a17e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0xff3516e3  bne a0,s3,8000056e *)
Lemma pkdb_ff3516e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff3516e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 10), BNE), s).
Proof. decode_bridge_ms. Qed.


Section WpPrintkDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PK := KernelSyms.printk.

  Lemma pki_00 : kernel_text -∗ instr (mword_of_int PK : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 52 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc PK (mword_of_int 0x7131 : mword 16)
    (mword_of_int PK : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 52 : mword 6), sp, sp, ADDI)) pkdc_7131 exec_execute_C_ADDI16SP. Qed.

  Lemma pki_02 : kernel_text -∗ instr (mword_of_int (PK + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PK + 0x02)%Z (mword_of_int 0xfc86 : mword 16)
    (mword_of_int (PK + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) pkdc_fc86 exec_execute_C_SDSP. Qed.

  Lemma pki_04 : kernel_text -∗ instr (mword_of_int (PK + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PK + 0x04)%Z (mword_of_int 0xf8a2 : mword 16)
    (mword_of_int (PK + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) pkdc_f8a2 exec_execute_C_SDSP. Qed.

  Lemma pki_06 : kernel_text -∗ instr (mword_of_int (PK + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PK + 0x06)%Z (mword_of_int 0xf0ca : mword 16)
    (mword_of_int (PK + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) pkdc_f0ca exec_execute_C_SDSP. Qed.

  Lemma pki_08 : kernel_text -∗ instr (mword_of_int (PK + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 32 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PK + 0x08)%Z (mword_of_int 0x0100 : mword 16)
    (mword_of_int (PK + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 32 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) pkdc_0100 exec_execute_C_ADDI4SPN. Qed.

  Lemma pki_0a : kernel_text -∗ instr (mword_of_int (PK + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PK + 0x0a)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (PK + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) pkdc_892a exec_execute_C_MV. Qed.

  Lemma pki_0c : kernel_text -∗ instr (mword_of_int (PK + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)).
  Proof. mk_rvc (PK + 0x0c)%Z (mword_of_int 0xe40c : mword 16)
    (mword_of_int (PK + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)) pkdc_e40c exec_execute_C_SD. Qed.

  Lemma pki_0e : kernel_text -∗ instr (mword_of_int (PK + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)).
  Proof. mk_rvc (PK + 0x0e)%Z (mword_of_int 0xe810 : mword 16)
    (mword_of_int (PK + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)) pkdc_e810 exec_execute_C_SD. Qed.

  Lemma pki_10 : kernel_text -∗ instr (mword_of_int (PK + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)).
  Proof. mk_rvc (PK + 0x10)%Z (mword_of_int 0xec14 : mword 16)
    (mword_of_int (PK + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)) pkdc_ec14 exec_execute_C_SD. Qed.

  Lemma pki_12 : kernel_text -∗ instr (mword_of_int (PK + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)).
  Proof. mk_rvc (PK + 0x12)%Z (mword_of_int 0xf018 : mword 16)
    (mword_of_int (PK + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)) pkdc_f018 exec_execute_C_SD. Qed.

  Lemma pki_14 : kernel_text -∗ instr (mword_of_int (PK + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)).
  Proof. mk_rvc (PK + 0x14)%Z (mword_of_int 0xf41c : mword 16)
    (mword_of_int (PK + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 0)), 8)) pkdc_f41c exec_execute_C_SD. Qed.

  Lemma pki_16 : kernel_text -∗ instr (mword_of_int (PK + 0x16) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x16)%Z (mword_of_int 0x03043823 : mword 32)
    (mword_of_int (PK + 0x16) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 16), Regidx (mword_of_int 8), 8)) pkdb_03043823. Qed.

  Lemma pki_1a : kernel_text -∗ instr (mword_of_int (PK + 0x1a) : mword 64) false (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x1a)%Z (mword_of_int 0x03143c23 : mword 32)
    (mword_of_int (PK + 0x1a) : mword 64) (STORE (mword_of_int 56 : mword 12, Regidx (mword_of_int 17), Regidx (mword_of_int 8), 8)) pkdb_03143c23. Qed.

  Lemma pki_1e : kernel_text -∗ instr (mword_of_int (PK + 0x1e) : mword 64) false (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (PK + 0x1e)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (PK + 0x1e) : mword 64) (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)) pkdb_0000a797. Qed.

  Lemma pki_22 : kernel_text -∗ instr (mword_of_int (PK + 0x22) : mword 64) false (LOAD (mword_of_int 3338 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PK + 0x22)%Z (mword_of_int 0xd0a7a783 : mword 32)
    (mword_of_int (PK + 0x22) : mword 64) (LOAD (mword_of_int 3338 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) pkdb_d0a7a783. Qed.

  Lemma pki_26 : kernel_text -∗ instr (mword_of_int (PK + 0x26) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 31 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PK + 0x26)%Z (mword_of_int 0xcf9d : mword 16)
    (mword_of_int (PK + 0x26) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 31 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) pkdc_cf9d exec_execute_C_BEQZ. Qed.

  Lemma pki_28 : kernel_text -∗ instr (mword_of_int (PK + 0x28) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PK + 0x28)%Z (mword_of_int 0x00840793 : mword 32)
    (mword_of_int (PK + 0x28) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), ADDI)) pkdb_00840793. Qed.

  Lemma pki_2c : kernel_text -∗ instr (mword_of_int (PK + 0x2c) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x2c)%Z (mword_of_int 0xf8f43423 : mword 32)
    (mword_of_int (PK + 0x2c) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 8)) pkdb_f8f43423. Qed.

  Lemma pki_30 : kernel_text -∗ instr (mword_of_int (PK + 0x30) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PK + 0x30)%Z (mword_of_int 0x00094503 : mword 32)
    (mword_of_int (PK + 0x30) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), true, 1)) pkdb_00094503. Qed.

  Lemma pki_34 : kernel_text -∗ instr (mword_of_int (PK + 0x34) : mword 64) false (BTYPE (mword_of_int 556 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (PK + 0x34)%Z (mword_of_int 0x22050663 : mword 32)
    (mword_of_int (PK + 0x34) : mword 64) (BTYPE (mword_of_int 556 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)) pkdb_22050663. Qed.

  Lemma pki_38 : kernel_text -∗ instr (mword_of_int (PK + 0x38) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PK + 0x38)%Z (mword_of_int 0xf4a6 : mword 16)
    (mword_of_int (PK + 0x38) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) pkdc_f4a6 exec_execute_C_SDSP. Qed.

  Lemma pki_3a : kernel_text -∗ instr (mword_of_int (PK + 0x3a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (PK + 0x3a)%Z (mword_of_int 0xecce : mword 16)
    (mword_of_int (PK + 0x3a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) pkdc_ecce exec_execute_C_SDSP. Qed.

  Lemma pki_3c : kernel_text -∗ instr (mword_of_int (PK + 0x3c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (PK + 0x3c)%Z (mword_of_int 0xe8d2 : mword 16)
    (mword_of_int (PK + 0x3c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) pkdc_e8d2 exec_execute_C_SDSP. Qed.

  Lemma pki_3e : kernel_text -∗ instr (mword_of_int (PK + 0x3e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (PK + 0x3e)%Z (mword_of_int 0xe4d6 : mword 16)
    (mword_of_int (PK + 0x3e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) pkdc_e4d6 exec_execute_C_SDSP. Qed.

  Lemma pki_40 : kernel_text -∗ instr (mword_of_int (PK + 0x40) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PK + 0x40)%Z (mword_of_int 0xe0da : mword 16)
    (mword_of_int (PK + 0x40) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) pkdc_e0da exec_execute_C_SDSP. Qed.

  Lemma pki_42 : kernel_text -∗ instr (mword_of_int (PK + 0x42) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (PK + 0x42)%Z (mword_of_int 0xfc5e : mword 16)
    (mword_of_int (PK + 0x42) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) pkdc_fc5e exec_execute_C_SDSP. Qed.

  Lemma pki_44 : kernel_text -∗ instr (mword_of_int (PK + 0x44) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (PK + 0x44)%Z (mword_of_int 0xf862 : mword 16)
    (mword_of_int (PK + 0x44) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) pkdc_f862 exec_execute_C_SDSP. Qed.

  Lemma pki_46 : kernel_text -∗ instr (mword_of_int (PK + 0x46) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)).
  Proof. mk_rvc (PK + 0x46)%Z (mword_of_int 0xf06a : mword 16)
    (mword_of_int (PK + 0x46) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)) pkdc_f06a exec_execute_C_SDSP. Qed.

  Lemma pki_48 : kernel_text -∗ instr (mword_of_int (PK + 0x48) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 27), sp, 8)).
  Proof. mk_rvc (PK + 0x48)%Z (mword_of_int 0xec6e : mword 16)
    (mword_of_int (PK + 0x48) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 27), sp, 8)) pkdc_ec6e exec_execute_C_SDSP. Qed.

  Lemma pki_4a : kernel_text -∗ instr (mword_of_int (PK + 0x4a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (PK + 0x4a)%Z (mword_of_int 0x4a01 : mword 16)
    (mword_of_int (PK + 0x4a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)) pkdc_4a01 exec_execute_C_LI. Qed.

  Lemma pki_4c : kernel_text -∗ instr (mword_of_int (PK + 0x4c) : mword 64) false (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (PK + 0x4c)%Z (mword_of_int 0x02500993 : mword 32)
    (mword_of_int (PK + 0x4c) : mword 64) (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 19), ADDI)) pkdb_02500993. Qed.

  Lemma pki_50 : kernel_text -∗ instr (mword_of_int (PK + 0x50) : mword 64) false (ITYPE (mword_of_int 117 : mword 12, zreg, Regidx (mword_of_int 24), ADDI)).
  Proof. mk_base (PK + 0x50)%Z (mword_of_int 0x07500c13 : mword 32)
    (mword_of_int (PK + 0x50) : mword 64) (ITYPE (mword_of_int 117 : mword 12, zreg, Regidx (mword_of_int 24), ADDI)) pkdb_07500c13. Qed.

  Lemma pki_54 : kernel_text -∗ instr (mword_of_int (PK + 0x54) : mword 64) false (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 26), ADDI)).
  Proof. mk_base (PK + 0x54)%Z (mword_of_int 0x07800d13 : mword 32)
    (mword_of_int (PK + 0x54) : mword 64) (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 26), ADDI)) pkdb_07800d13. Qed.

  Lemma pki_58 : kernel_text -∗ instr (mword_of_int (PK + 0x58) : mword 64) false (ITYPE (mword_of_int 112 : mword 12, zreg, Regidx (mword_of_int 27), ADDI)).
  Proof. mk_base (PK + 0x58)%Z (mword_of_int 0x07000d93 : mword 32)
    (mword_of_int (PK + 0x58) : mword 64) (ITYPE (mword_of_int 112 : mword 12, zreg, Regidx (mword_of_int 27), ADDI)) pkdb_07000d93. Qed.

  Lemma pki_5c : kernel_text -∗ instr (mword_of_int (PK + 0x5c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)).
  Proof. mk_rvc (PK + 0x5c)%Z (mword_of_int 0x4b29 : mword 16)
    (mword_of_int (PK + 0x5c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)) pkdc_4b29 exec_execute_C_LI. Qed.

  Lemma pki_5e : kernel_text -∗ instr (mword_of_int (PK + 0x5e) : mword 64) false (ITYPE (mword_of_int 100 : mword 12, zreg, Regidx (mword_of_int 23), ADDI)).
  Proof. mk_base (PK + 0x5e)%Z (mword_of_int 0x06400b93 : mword 32)
    (mword_of_int (PK + 0x5e) : mword 64) (ITYPE (mword_of_int 100 : mword 12, zreg, Regidx (mword_of_int 23), ADDI)) pkdb_06400b93. Qed.

  Lemma pki_62 : kernel_text -∗ instr (mword_of_int (PK + 0x62) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x62)%Z (mword_of_int 0xa015 : mword 16)
    (mword_of_int (PK + 0x62) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")), zreg)) pkdc_a015 exec_execute_C_J. Qed.

  Lemma pki_64 : kernel_text -∗ instr (mword_of_int (PK + 0x64) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (PK + 0x64)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (PK + 0x64) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma pki_68 : kernel_text -∗ instr (mword_of_int (PK + 0x68) : mword 64) false (ITYPE (mword_of_int 3480 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x68)%Z (mword_of_int 0xd9850513 : mword 32)
    (mword_of_int (PK + 0x68) : mword 64) (ITYPE (mword_of_int 3480 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) pkdb_d9850513. Qed.

  Lemma pki_6c : kernel_text -∗ instr (mword_of_int (PK + 0x6c) : mword 64) false (JAL (mword_of_int 1696 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x6c)%Z (mword_of_int 0x6a0000ef : mword 32)
    (mword_of_int (PK + 0x6c) : mword 64) (JAL (mword_of_int 1696 : mword 21, Regidx (mword_of_int 1))) pkdb_6a0000ef. Qed.

  Lemma pki_70 : kernel_text -∗ instr (mword_of_int (PK + 0x70) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2012 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x70)%Z (mword_of_int 0xbf65 : mword 16)
    (mword_of_int (PK + 0x70) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2012 : mword 11) ('b"0")), zreg)) pkdc_bf65 exec_execute_C_J. Qed.

  Lemma pki_72 : kernel_text -∗ instr (mword_of_int (PK + 0x72) : mword 64) false (JAL (mword_of_int 2096398 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x72)%Z (mword_of_int 0xd0fff0ef : mword 32)
    (mword_of_int (PK + 0x72) : mword 64) (JAL (mword_of_int 2096398 : mword 21, Regidx (mword_of_int 1))) pkdb_d0fff0ef. Qed.

  Lemma pki_76 : kernel_text -∗ instr (mword_of_int (PK + 0x76) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PK + 0x76)%Z (mword_of_int 0x84d2 : mword 16)
    (mword_of_int (PK + 0x76) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 9), ADD)) pkdc_84d2 exec_execute_C_MV. Qed.

  Lemma pki_78 : kernel_text -∗ instr (mword_of_int (PK + 0x78) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9))).
  Proof. mk_rvc (PK + 0x78)%Z (mword_of_int 0x2485 : mword 16)
    (mword_of_int (PK + 0x78) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9))) pkdc_2485 exec_execute_C_ADDIW. Qed.

  Lemma pki_7a : kernel_text -∗ instr (mword_of_int (PK + 0x7a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (PK + 0x7a)%Z (mword_of_int 0x8a26 : mword 16)
    (mword_of_int (PK + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 20), ADD)) pkdc_8a26 exec_execute_C_MV. Qed.

  Lemma pki_7c : kernel_text -∗ instr (mword_of_int (PK + 0x7c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PK + 0x7c)%Z (mword_of_int 0x94ca : mword 16)
    (mword_of_int (PK + 0x7c) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) pkdc_94ca exec_execute_C_ADD. Qed.

  Lemma pki_7e : kernel_text -∗ instr (mword_of_int (PK + 0x7e) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PK + 0x7e)%Z (mword_of_int 0x0004c503 : mword 32)
    (mword_of_int (PK + 0x7e) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), true, 1)) pkdb_0004c503. Qed.

  Lemma pki_82 : kernel_text -∗ instr (mword_of_int (PK + 0x82) : mword 64) false (BTYPE (mword_of_int 460 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (PK + 0x82)%Z (mword_of_int 0x1c050663 : mword 32)
    (mword_of_int (PK + 0x82) : mword 64) (BTYPE (mword_of_int 460 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)) pkdb_1c050663. Qed.

  Lemma pki_86 : kernel_text -∗ instr (mword_of_int (PK + 0x86) : mword 64) false (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 10), BNE)).
  Proof. mk_base (PK + 0x86)%Z (mword_of_int 0xff3516e3 : mword 32)
    (mword_of_int (PK + 0x86) : mword 64) (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 10), BNE)) pkdb_ff3516e3. Qed.

  Lemma pki_8a : kernel_text -∗ instr (mword_of_int (PK + 0x8a) : mword 64) false (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15))).
  Proof. mk_base (PK + 0x8a)%Z (mword_of_int 0x001a079b : mword 32)
    (mword_of_int (PK + 0x8a) : mword 64) (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15))) pkdb_001a079b. Qed.

  Lemma pki_8e : kernel_text -∗ instr (mword_of_int (PK + 0x8e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PK + 0x8e)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (PK + 0x8e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) cdec_84be exec_execute_C_MV. Qed.

  Lemma pki_90 : kernel_text -∗ instr (mword_of_int (PK + 0x90) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (PK + 0x90)%Z (mword_of_int 0x00f90733 : mword 32)
    (mword_of_int (PK + 0x90) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 14), ADD)) pkdb_00f90733. Qed.

  Lemma pki_94 : kernel_text -∗ instr (mword_of_int (PK + 0x94) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 21), true, 1)).
  Proof. mk_base (PK + 0x94)%Z (mword_of_int 0x00074a83 : mword 32)
    (mword_of_int (PK + 0x94) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 21), true, 1)) pkdb_00074a83. Qed.

  Lemma pki_98 : kernel_text -∗ instr (mword_of_int (PK + 0x98) : mword 64) false (BTYPE (mword_of_int 530 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x98)%Z (mword_of_int 0x200a8963 : mword 32)
    (mword_of_int (PK + 0x98) : mword 64) (BTYPE (mword_of_int 530 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)) pkdb_200a8963. Qed.

  Lemma pki_9c : kernel_text -∗ instr (mword_of_int (PK + 0x9c) : mword 64) false (LOAD (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1)).
  Proof. mk_base (PK + 0x9c)%Z (mword_of_int 0x00174683 : mword 32)
    (mword_of_int (PK + 0x9c) : mword 64) (LOAD (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 13), true, 1)) pkdb_00174683. Qed.

  Lemma pki_a0 : kernel_text -∗ instr (mword_of_int (PK + 0xa0) : mword 64) false (BTYPE (mword_of_int 504 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 13), BEQ)).
  Proof. mk_base (PK + 0xa0)%Z (mword_of_int 0x1e068c63 : mword 32)
    (mword_of_int (PK + 0xa0) : mword 64) (BTYPE (mword_of_int 504 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 13), BEQ)) pkdb_1e068c63. Qed.

  Lemma pki_a4 : kernel_text -∗ instr (mword_of_int (PK + 0xa4) : mword 64) false (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0xa4)%Z (mword_of_int 0x037a8863 : mword 32)
    (mword_of_int (PK + 0xa4) : mword 64) (BTYPE (mword_of_int 48 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ)) pkdb_037a8863. Qed.

  Lemma pki_a8 : kernel_text -∗ instr (mword_of_int (PK + 0xa8) : mword 64) false (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0xa8)%Z (mword_of_int 0xf94a8713 : mword 32)
    (mword_of_int (PK + 0xa8) : mword 64) (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)) pkdb_f94a8713. Qed.

  Lemma pki_ac : kernel_text -∗ instr (mword_of_int (PK + 0xac) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)).
  Proof. mk_base (PK + 0xac)%Z (mword_of_int 0x00173713 : mword 32)
    (mword_of_int (PK + 0xac) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)) pkdb_00173713. Qed.

  Lemma pki_b0 : kernel_text -∗ instr (mword_of_int (PK + 0xb0) : mword 64) false (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (PK + 0xb0)%Z (mword_of_int 0xf9c68613 : mword 32)
    (mword_of_int (PK + 0xb0) : mword 64) (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 12), ADDI)) pkdb_f9c68613. Qed.

  Lemma pki_b4 : kernel_text -∗ instr (mword_of_int (PK + 0xb4) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BNE)).
  Proof. mk_rvc (PK + 0xb4)%Z (mword_of_int 0xee05 : mword 16)
    (mword_of_int (PK + 0xb4) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BNE)) pkdc_ee05 exec_execute_C_BNEZ. Qed.

  Lemma pki_b6 : kernel_text -∗ instr (mword_of_int (PK + 0xb6) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 27 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).
  Proof. mk_rvc (PK + 0xb6)%Z (mword_of_int 0xcb1d : mword 16)
    (mword_of_int (PK + 0xb6) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 27 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) pkdc_cb1d exec_execute_C_BEQZ. Qed.

  Lemma pki_b8 : kernel_text -∗ instr (mword_of_int (PK + 0xb8) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0xb8)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0xb8) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_bc : kernel_text -∗ instr (mword_of_int (PK + 0xbc) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0xbc)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0xbc) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_c0 : kernel_text -∗ instr (mword_of_int (PK + 0xc0) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0xc0)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0xc0) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_c4 : kernel_text -∗ instr (mword_of_int (PK + 0xc4) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0xc4)%Z (mword_of_int 0x4605 : mword 16)
    (mword_of_int (PK + 0xc4) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) pkdc_4605 exec_execute_C_LI. Qed.

  Lemma pki_c6 : kernel_text -∗ instr (mword_of_int (PK + 0xc6) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PK + 0xc6)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (PK + 0xc6) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) cdec_85da exec_execute_C_MV. Qed.

  Lemma pki_c8 : kernel_text -∗ instr (mword_of_int (PK + 0xc8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0xc8)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0xc8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_ca : kernel_text -∗ instr (mword_of_int (PK + 0xca) : mword 64) false (JAL (mword_of_int 2096800 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0xca)%Z (mword_of_int 0xea1ff0ef : mword 32)
    (mword_of_int (PK + 0xca) : mword 64) (JAL (mword_of_int 2096800 : mword 21, Regidx (mword_of_int 1))) pkdb_ea1ff0ef. Qed.

  Lemma pki_ce : kernel_text -∗ instr (mword_of_int (PK + 0xce) : mword 64) false (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0xce)%Z (mword_of_int 0x002a049b : mword 32)
    (mword_of_int (PK + 0xce) : mword 64) (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_002a049b. Qed.

  Lemma pki_d2 : kernel_text -∗ instr (mword_of_int (PK + 0xd2) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0xd2)%Z (mword_of_int 0xb75d : mword 16)
    (mword_of_int (PK + 0xd2) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2003 : mword 11) ('b"0")), zreg)) pkdc_b75d exec_execute_C_J. Qed.

  Lemma pki_d4 : kernel_text -∗ instr (mword_of_int (PK + 0xd4) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0xd4)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0xd4) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_d8 : kernel_text -∗ instr (mword_of_int (PK + 0xd8) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0xd8)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0xd8) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_dc : kernel_text -∗ instr (mword_of_int (PK + 0xdc) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0xdc)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0xdc) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_e0 : kernel_text -∗ instr (mword_of_int (PK + 0xe0) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0xe0)%Z (mword_of_int 0x4605 : mword 16)
    (mword_of_int (PK + 0xe0) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) pkdc_4605 exec_execute_C_LI. Qed.

  Lemma pki_e2 : kernel_text -∗ instr (mword_of_int (PK + 0xe2) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PK + 0xe2)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (PK + 0xe2) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) cdec_85da exec_execute_C_MV. Qed.

  Lemma pki_e4 : kernel_text -∗ instr (mword_of_int (PK + 0xe4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)).
  Proof. mk_rvc (PK + 0xe4)%Z (mword_of_int 0x4388 : mword 16)
    (mword_of_int (PK + 0xe4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)) pkdc_4388 exec_execute_C_LW. Qed.

  Lemma pki_e6 : kernel_text -∗ instr (mword_of_int (PK + 0xe6) : mword 64) false (JAL (mword_of_int 2096772 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0xe6)%Z (mword_of_int 0xe85ff0ef : mword 32)
    (mword_of_int (PK + 0xe6) : mword 64) (JAL (mword_of_int 2096772 : mword 21, Regidx (mword_of_int 1))) pkdb_e85ff0ef. Qed.

  Lemma pki_ea : kernel_text -∗ instr (mword_of_int (PK + 0xea) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0xea)%Z (mword_of_int 0xb779 : mword 16)
    (mword_of_int (PK + 0xea) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)) pkdc_b779 exec_execute_C_J. Qed.

  Lemma pki_ec : kernel_text -∗ instr (mword_of_int (PK + 0xec) : mword 64) true (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PK + 0xec)%Z (mword_of_int 0x97ca : mword 16)
    (mword_of_int (PK + 0xec) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) pkdc_97ca exec_execute_C_ADD. Qed.

  Lemma pki_ee : kernel_text -∗ instr (mword_of_int (PK + 0xee) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (PK + 0xee)%Z (mword_of_int 0x8636 : mword 16)
    (mword_of_int (PK + 0xee) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 12), ADD)) pkdc_8636 exec_execute_C_MV. Qed.

  Lemma pki_f0 : kernel_text -∗ instr (mword_of_int (PK + 0xf0) : mword 64) false (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), true, 1)).
  Proof. mk_base (PK + 0xf0)%Z (mword_of_int 0x0027c683 : mword 32)
    (mword_of_int (PK + 0xf0) : mword 64) (LOAD (mword_of_int 2 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 13), true, 1)) pkdb_0027c683. Qed.

  Lemma pki_f4 : kernel_text -∗ instr (mword_of_int (PK + 0xf4) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 225 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0xf4)%Z (mword_of_int 0xa2c9 : mword 16)
    (mword_of_int (PK + 0xf4) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 225 : mword 11) ('b"0")), zreg)) pkdc_a2c9 exec_execute_C_J. Qed.

  Lemma pki_f6 : kernel_text -∗ instr (mword_of_int (PK + 0xf6) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0xf6)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0xf6) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_fa : kernel_text -∗ instr (mword_of_int (PK + 0xfa) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0xfa)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0xfa) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_fe : kernel_text -∗ instr (mword_of_int (PK + 0xfe) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0xfe)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0xfe) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_102 : kernel_text -∗ instr (mword_of_int (PK + 0x102) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x102)%Z (mword_of_int 0x4605 : mword 16)
    (mword_of_int (PK + 0x102) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) pkdc_4605 exec_execute_C_LI. Qed.

  Lemma pki_104 : kernel_text -∗ instr (mword_of_int (PK + 0x104) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (PK + 0x104)%Z (mword_of_int 0x45a9 : mword 16)
    (mword_of_int (PK + 0x104) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) pkdc_45a9 exec_execute_C_LI. Qed.

  Lemma pki_106 : kernel_text -∗ instr (mword_of_int (PK + 0x106) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0x106)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0x106) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_108 : kernel_text -∗ instr (mword_of_int (PK + 0x108) : mword 64) false (JAL (mword_of_int 2096738 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x108)%Z (mword_of_int 0xe63ff0ef : mword 32)
    (mword_of_int (PK + 0x108) : mword 64) (JAL (mword_of_int 2096738 : mword 21, Regidx (mword_of_int 1))) pkdb_e63ff0ef. Qed.

  Lemma pki_10c : kernel_text -∗ instr (mword_of_int (PK + 0x10c) : mword 64) false (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0x10c)%Z (mword_of_int 0x003a049b : mword 32)
    (mword_of_int (PK + 0x10c) : mword 64) (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_003a049b. Qed.

  Lemma pki_110 : kernel_text -∗ instr (mword_of_int (PK + 0x110) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x110)%Z (mword_of_int 0xb7a5 : mword 16)
    (mword_of_int (PK + 0x110) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1972 : mword 11) ('b"0")), zreg)) pkdc_b7a5 exec_execute_C_J. Qed.

  Lemma pki_112 : kernel_text -∗ instr (mword_of_int (PK + 0x112) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x112)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x112) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_116 : kernel_text -∗ instr (mword_of_int (PK + 0x116) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x116)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x116) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_11a : kernel_text -∗ instr (mword_of_int (PK + 0x11a) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x11a)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x11a) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_11e : kernel_text -∗ instr (mword_of_int (PK + 0x11e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x11e)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (PK + 0x11e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma pki_120 : kernel_text -∗ instr (mword_of_int (PK + 0x120) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PK + 0x120)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (PK + 0x120) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) cdec_85da exec_execute_C_MV. Qed.

  Lemma pki_122 : kernel_text -∗ instr (mword_of_int (PK + 0x122) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 4)).
  Proof. mk_base (PK + 0x122)%Z (mword_of_int 0x0007e503 : mword 32)
    (mword_of_int (PK + 0x122) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 4)) pkdb_0007e503. Qed.

  Lemma pki_126 : kernel_text -∗ instr (mword_of_int (PK + 0x126) : mword 64) false (JAL (mword_of_int 2096708 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x126)%Z (mword_of_int 0xe45ff0ef : mword 32)
    (mword_of_int (PK + 0x126) : mword 64) (JAL (mword_of_int 2096708 : mword 21, Regidx (mword_of_int 1))) pkdb_e45ff0ef. Qed.

  Lemma pki_12a : kernel_text -∗ instr (mword_of_int (PK + 0x12a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x12a)%Z (mword_of_int 0xb7b9 : mword 16)
    (mword_of_int (PK + 0x12a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1959 : mword 11) ('b"0")), zreg)) pkdc_b7b9 exec_execute_C_J. Qed.

  Lemma pki_12c : kernel_text -∗ instr (mword_of_int (PK + 0x12c) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x12c)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x12c) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_130 : kernel_text -∗ instr (mword_of_int (PK + 0x130) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x130)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x130) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_134 : kernel_text -∗ instr (mword_of_int (PK + 0x134) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x134)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x134) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_138 : kernel_text -∗ instr (mword_of_int (PK + 0x138) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x138)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (PK + 0x138) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma pki_13a : kernel_text -∗ instr (mword_of_int (PK + 0x13a) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PK + 0x13a)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (PK + 0x13a) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) cdec_85da exec_execute_C_MV. Qed.

  Lemma pki_13c : kernel_text -∗ instr (mword_of_int (PK + 0x13c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0x13c)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0x13c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_13e : kernel_text -∗ instr (mword_of_int (PK + 0x13e) : mword 64) false (JAL (mword_of_int 2096684 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x13e)%Z (mword_of_int 0xe2dff0ef : mword 32)
    (mword_of_int (PK + 0x13e) : mword 64) (JAL (mword_of_int 2096684 : mword 21, Regidx (mword_of_int 1))) pkdb_e2dff0ef. Qed.

  Lemma pki_142 : kernel_text -∗ instr (mword_of_int (PK + 0x142) : mword 64) false (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0x142)%Z (mword_of_int 0x002a049b : mword 32)
    (mword_of_int (PK + 0x142) : mword 64) (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_002a049b. Qed.

  Lemma pki_146 : kernel_text -∗ instr (mword_of_int (PK + 0x146) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x146)%Z (mword_of_int 0xbf0d : mword 16)
    (mword_of_int (PK + 0x146) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1945 : mword 11) ('b"0")), zreg)) pkdc_bf0d exec_execute_C_J. Qed.

  Lemma pki_148 : kernel_text -∗ instr (mword_of_int (PK + 0x148) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x148)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x148) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_14c : kernel_text -∗ instr (mword_of_int (PK + 0x14c) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x14c)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x14c) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_150 : kernel_text -∗ instr (mword_of_int (PK + 0x150) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x150)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x150) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_154 : kernel_text -∗ instr (mword_of_int (PK + 0x154) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x154)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (PK + 0x154) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma pki_156 : kernel_text -∗ instr (mword_of_int (PK + 0x156) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (PK + 0x156)%Z (mword_of_int 0x45a9 : mword 16)
    (mword_of_int (PK + 0x156) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 10 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) pkdc_45a9 exec_execute_C_LI. Qed.

  Lemma pki_158 : kernel_text -∗ instr (mword_of_int (PK + 0x158) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0x158)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0x158) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_15a : kernel_text -∗ instr (mword_of_int (PK + 0x15a) : mword 64) false (JAL (mword_of_int 2096656 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x15a)%Z (mword_of_int 0xe11ff0ef : mword 32)
    (mword_of_int (PK + 0x15a) : mword 64) (JAL (mword_of_int 2096656 : mword 21, Regidx (mword_of_int 1))) pkdb_e11ff0ef. Qed.

  Lemma pki_15e : kernel_text -∗ instr (mword_of_int (PK + 0x15e) : mword 64) false (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0x15e)%Z (mword_of_int 0x003a049b : mword 32)
    (mword_of_int (PK + 0x15e) : mword 64) (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_003a049b. Qed.

  Lemma pki_162 : kernel_text -∗ instr (mword_of_int (PK + 0x162) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x162)%Z (mword_of_int 0xbf19 : mword 16)
    (mword_of_int (PK + 0x162) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1931 : mword 11) ('b"0")), zreg)) pkdc_bf19 exec_execute_C_J. Qed.

  Lemma pki_164 : kernel_text -∗ instr (mword_of_int (PK + 0x164) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x164)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x164) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_168 : kernel_text -∗ instr (mword_of_int (PK + 0x168) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x168)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x168) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_16c : kernel_text -∗ instr (mword_of_int (PK + 0x16c) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x16c)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x16c) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_170 : kernel_text -∗ instr (mword_of_int (PK + 0x170) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x170)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (PK + 0x170) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma pki_172 : kernel_text -∗ instr (mword_of_int (PK + 0x172) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (PK + 0x172)%Z (mword_of_int 0x45c1 : mword 16)
    (mword_of_int (PK + 0x172) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) pkdc_45c1 exec_execute_C_LI. Qed.

  Lemma pki_174 : kernel_text -∗ instr (mword_of_int (PK + 0x174) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 4)).
  Proof. mk_base (PK + 0x174)%Z (mword_of_int 0x0007e503 : mword 32)
    (mword_of_int (PK + 0x174) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 4)) pkdb_0007e503. Qed.

  Lemma pki_178 : kernel_text -∗ instr (mword_of_int (PK + 0x178) : mword 64) false (JAL (mword_of_int 2096626 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x178)%Z (mword_of_int 0xdf3ff0ef : mword 32)
    (mword_of_int (PK + 0x178) : mword 64) (JAL (mword_of_int 2096626 : mword 21, Regidx (mword_of_int 1))) pkdb_df3ff0ef. Qed.

  Lemma pki_17c : kernel_text -∗ instr (mword_of_int (PK + 0x17c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x17c)%Z (mword_of_int 0xbdf5 : mword 16)
    (mword_of_int (PK + 0x17c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1918 : mword 11) ('b"0")), zreg)) pkdc_bdf5 exec_execute_C_J. Qed.

  Lemma pki_17e : kernel_text -∗ instr (mword_of_int (PK + 0x17e) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x17e)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x17e) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_182 : kernel_text -∗ instr (mword_of_int (PK + 0x182) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x182)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x182) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_186 : kernel_text -∗ instr (mword_of_int (PK + 0x186) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x186)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x186) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_18a : kernel_text -∗ instr (mword_of_int (PK + 0x18a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (PK + 0x18a)%Z (mword_of_int 0x45c1 : mword 16)
    (mword_of_int (PK + 0x18a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) pkdc_45c1 exec_execute_C_LI. Qed.

  Lemma pki_18c : kernel_text -∗ instr (mword_of_int (PK + 0x18c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0x18c)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0x18c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_18e : kernel_text -∗ instr (mword_of_int (PK + 0x18e) : mword 64) false (JAL (mword_of_int 2096604 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x18e)%Z (mword_of_int 0xdddff0ef : mword 32)
    (mword_of_int (PK + 0x18e) : mword 64) (JAL (mword_of_int 2096604 : mword 21, Regidx (mword_of_int 1))) pkdb_dddff0ef. Qed.

  Lemma pki_192 : kernel_text -∗ instr (mword_of_int (PK + 0x192) : mword 64) false (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0x192)%Z (mword_of_int 0x002a049b : mword 32)
    (mword_of_int (PK + 0x192) : mword 64) (ADDIW (mword_of_int 2 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_002a049b. Qed.

  Lemma pki_196 : kernel_text -∗ instr (mword_of_int (PK + 0x196) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x196)%Z (mword_of_int 0xb5cd : mword 16)
    (mword_of_int (PK + 0x196) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1905 : mword 11) ('b"0")), zreg)) pkdc_b5cd exec_execute_C_J. Qed.

  Lemma pki_198 : kernel_text -∗ instr (mword_of_int (PK + 0x198) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x198)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x198) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_19c : kernel_text -∗ instr (mword_of_int (PK + 0x19c) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x19c)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x19c) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_1a0 : kernel_text -∗ instr (mword_of_int (PK + 0x1a0) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x1a0)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x1a0) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_1a4 : kernel_text -∗ instr (mword_of_int (PK + 0x1a4) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (PK + 0x1a4)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (PK + 0x1a4) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma pki_1a6 : kernel_text -∗ instr (mword_of_int (PK + 0x1a6) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (PK + 0x1a6)%Z (mword_of_int 0x45c1 : mword 16)
    (mword_of_int (PK + 0x1a6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) pkdc_45c1 exec_execute_C_LI. Qed.

  Lemma pki_1a8 : kernel_text -∗ instr (mword_of_int (PK + 0x1a8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (PK + 0x1a8)%Z (mword_of_int 0x6388 : mword 16)
    (mword_of_int (PK + 0x1a8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) pkdc_6388 exec_execute_C_LD. Qed.

  Lemma pki_1aa : kernel_text -∗ instr (mword_of_int (PK + 0x1aa) : mword 64) false (JAL (mword_of_int 2096576 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x1aa)%Z (mword_of_int 0xdc1ff0ef : mword 32)
    (mword_of_int (PK + 0x1aa) : mword 64) (JAL (mword_of_int 2096576 : mword 21, Regidx (mword_of_int 1))) pkdb_dc1ff0ef. Qed.

  Lemma pki_1ae : kernel_text -∗ instr (mword_of_int (PK + 0x1ae) : mword 64) false (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))).
  Proof. mk_base (PK + 0x1ae)%Z (mword_of_int 0x003a049b : mword 32)
    (mword_of_int (PK + 0x1ae) : mword 64) (ADDIW (mword_of_int 3 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 9))) pkdb_003a049b. Qed.

  Lemma pki_1b2 : kernel_text -∗ instr (mword_of_int (PK + 0x1b2) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x1b2)%Z (mword_of_int 0xb5d9 : mword 16)
    (mword_of_int (PK + 0x1b2) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1891 : mword 11) ('b"0")), zreg)) pkdc_b5d9 exec_execute_C_J. Qed.

  Lemma pki_1b4 : kernel_text -∗ instr (mword_of_int (PK + 0x1b4) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)).
  Proof. mk_rvc (PK + 0x1b4)%Z (mword_of_int 0xf466 : mword 16)
    (mword_of_int (PK + 0x1b4) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)) pkdc_f466 exec_execute_C_SDSP. Qed.

  Lemma pki_1b6 : kernel_text -∗ instr (mword_of_int (PK + 0x1b6) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x1b6)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x1b6) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_1ba : kernel_text -∗ instr (mword_of_int (PK + 0x1ba) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x1ba)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x1ba) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_1be : kernel_text -∗ instr (mword_of_int (PK + 0x1be) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x1be)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x1be) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_1c2 : kernel_text -∗ instr (mword_of_int (PK + 0x1c2) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 21), false, 8)).
  Proof. mk_base (PK + 0x1c2)%Z (mword_of_int 0x0007ba83 : mword 32)
    (mword_of_int (PK + 0x1c2) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 21), false, 8)) pkdb_0007ba83. Qed.

  Lemma pki_1c6 : kernel_text -∗ instr (mword_of_int (PK + 0x1c6) : mword 64) false (ITYPE (mword_of_int 48 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x1c6)%Z (mword_of_int 0x03000513 : mword 32)
    (mword_of_int (PK + 0x1c6) : mword 64) (ITYPE (mword_of_int 48 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)) pkdb_03000513. Qed.

  Lemma pki_1ca : kernel_text -∗ instr (mword_of_int (PK + 0x1ca) : mword 64) false (JAL (mword_of_int 2096054 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x1ca)%Z (mword_of_int 0xbb7ff0ef : mword 32)
    (mword_of_int (PK + 0x1ca) : mword 64) (JAL (mword_of_int 2096054 : mword 21, Regidx (mword_of_int 1))) pkdb_bb7ff0ef. Qed.

  Lemma pki_1ce : kernel_text -∗ instr (mword_of_int (PK + 0x1ce) : mword 64) false (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x1ce)%Z (mword_of_int 0x07800513 : mword 32)
    (mword_of_int (PK + 0x1ce) : mword 64) (ITYPE (mword_of_int 120 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)) pkdb_07800513. Qed.

  Lemma pki_1d2 : kernel_text -∗ instr (mword_of_int (PK + 0x1d2) : mword 64) false (JAL (mword_of_int 2096046 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x1d2)%Z (mword_of_int 0xbafff0ef : mword 32)
    (mword_of_int (PK + 0x1d2) : mword 64) (JAL (mword_of_int 2096046 : mword 21, Regidx (mword_of_int 1))) pkdb_bafff0ef. Qed.

  Lemma pki_1d6 : kernel_text -∗ instr (mword_of_int (PK + 0x1d6) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (PK + 0x1d6)%Z (mword_of_int 0x4a41 : mword 16)
    (mword_of_int (PK + 0x1d6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), zreg, Regidx (mword_of_int 20), ADDI)) pkdc_4a41 exec_execute_C_LI. Qed.

  Lemma pki_1d8 : kernel_text -∗ instr (mword_of_int (PK + 0x1d8) : mword 64) false (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 25), AUIPC)).
  Proof. mk_base (PK + 0x1d8)%Z (mword_of_int 0x00007c97 : mword 32)
    (mword_of_int (PK + 0x1d8) : mword 64) (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 25), AUIPC)) pkdb_00007c97. Qed.

  Lemma pki_1dc : kernel_text -∗ instr (mword_of_int (PK + 0x1dc) : mword 64) false (ITYPE (mword_of_int 60 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 25), ADDI)).
  Proof. mk_base (PK + 0x1dc)%Z (mword_of_int 0x03cc8c93 : mword 32)
    (mword_of_int (PK + 0x1dc) : mword 64) (ITYPE (mword_of_int 60 : mword 12, Regidx (mword_of_int 25), Regidx (mword_of_int 25), ADDI)) pkdb_03cc8c93. Qed.

  Lemma pki_1e0 : kernel_text -∗ instr (mword_of_int (PK + 0x1e0) : mword 64) false (SHIFTIOP (mword_of_int 60 : mword 6, Regidx (mword_of_int 21), Regidx (mword_of_int 15), SRLI)).
  Proof. mk_base (PK + 0x1e0)%Z (mword_of_int 0x03cad793 : mword 32)
    (mword_of_int (PK + 0x1e0) : mword 64) (SHIFTIOP (mword_of_int 60 : mword 6, Regidx (mword_of_int 21), Regidx (mword_of_int 15), SRLI)) pkdb_03cad793. Qed.

  Lemma pki_1e4 : kernel_text -∗ instr (mword_of_int (PK + 0x1e4) : mword 64) true (RTYPE (Regidx (mword_of_int 25), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PK + 0x1e4)%Z (mword_of_int 0x97e6 : mword 16)
    (mword_of_int (PK + 0x1e4) : mword 64) (RTYPE (Regidx (mword_of_int 25), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) pkdc_97e6 exec_execute_C_ADD. Qed.

  Lemma pki_1e6 : kernel_text -∗ instr (mword_of_int (PK + 0x1e6) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PK + 0x1e6)%Z (mword_of_int 0x0007c503 : mword 32)
    (mword_of_int (PK + 0x1e6) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), true, 1)) pkdb_0007c503. Qed.

  Lemma pki_1ea : kernel_text -∗ instr (mword_of_int (PK + 0x1ea) : mword 64) false (JAL (mword_of_int 2096022 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x1ea)%Z (mword_of_int 0xb97ff0ef : mword 32)
    (mword_of_int (PK + 0x1ea) : mword 64) (JAL (mword_of_int 2096022 : mword 21, Regidx (mword_of_int 1))) pkdb_b97ff0ef. Qed.

  Lemma pki_1ee : kernel_text -∗ instr (mword_of_int (PK + 0x1ee) : mword 64) true (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 21), Regidx (mword_of_int 21), SLLI)).
  Proof. mk_rvc (PK + 0x1ee)%Z (mword_of_int 0x0a92 : mword 16)
    (mword_of_int (PK + 0x1ee) : mword 64) (SHIFTIOP (mword_of_int 4 : mword 6, Regidx (mword_of_int 21), Regidx (mword_of_int 21), SLLI)) pkdc_0a92 exec_execute_C_SLLI. Qed.

  Lemma pki_1f0 : kernel_text -∗ instr (mword_of_int (PK + 0x1f0) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20))).
  Proof. mk_rvc (PK + 0x1f0)%Z (mword_of_int 0x3a7d : mword 16)
    (mword_of_int (PK + 0x1f0) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20))) pkdc_3a7d exec_execute_C_ADDIW. Qed.

  Lemma pki_1f2 : kernel_text -∗ instr (mword_of_int (PK + 0x1f2) : mword 64) false (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BNE)).
  Proof. mk_base (PK + 0x1f2)%Z (mword_of_int 0xfe0a17e3 : mword 32)
    (mword_of_int (PK + 0x1f2) : mword 64) (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BNE)) pkdb_fe0a17e3. Qed.

  Lemma pki_1f6 : kernel_text -∗ instr (mword_of_int (PK + 0x1f6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (PK + 0x1f6)%Z (mword_of_int 0x7ca2 : mword 16)
    (mword_of_int (PK + 0x1f6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) pkdc_7ca2 exec_execute_C_LDSP. Qed.

  Lemma pki_1f8 : kernel_text -∗ instr (mword_of_int (PK + 0x1f8) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1856 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x1f8)%Z (mword_of_int 0xb541 : mword 16)
    (mword_of_int (PK + 0x1f8) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1856 : mword 11) ('b"0")), zreg)) pkdc_b541 exec_execute_C_J. Qed.

  Lemma pki_1fa : kernel_text -∗ instr (mword_of_int (PK + 0x1fa) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x1fa)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x1fa) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_1fe : kernel_text -∗ instr (mword_of_int (PK + 0x1fe) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x1fe)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x1fe) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_202 : kernel_text -∗ instr (mword_of_int (PK + 0x202) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x202)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x202) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_206 : kernel_text -∗ instr (mword_of_int (PK + 0x206) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)).
  Proof. mk_rvc (PK + 0x206)%Z (mword_of_int 0x4388 : mword 16)
    (mword_of_int (PK + 0x206) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 4)) pkdc_4388 exec_execute_C_LW. Qed.

  Lemma pki_208 : kernel_text -∗ instr (mword_of_int (PK + 0x208) : mword 64) false (JAL (mword_of_int 2095992 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x208)%Z (mword_of_int 0xb79ff0ef : mword 32)
    (mword_of_int (PK + 0x208) : mword 64) (JAL (mword_of_int 2095992 : mword 21, Regidx (mword_of_int 1))) pkdb_b79ff0ef. Qed.

  Lemma pki_20c : kernel_text -∗ instr (mword_of_int (PK + 0x20c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x20c)%Z (mword_of_int 0xb5b5 : mword 16)
    (mword_of_int (PK + 0x20c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1846 : mword 11) ('b"0")), zreg)) pkdc_b5b5 exec_execute_C_J. Qed.

  Lemma pki_20e : kernel_text -∗ instr (mword_of_int (PK + 0x20e) : mword 64) false (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PK + 0x20e)%Z (mword_of_int 0xf8843783 : mword 32)
    (mword_of_int (PK + 0x20e) : mword 64) (LOAD (mword_of_int 3976 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 8)) pkdb_f8843783. Qed.

  Lemma pki_212 : kernel_text -∗ instr (mword_of_int (PK + 0x212) : mword 64) false (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x212)%Z (mword_of_int 0x00878713 : mword 32)
    (mword_of_int (PK + 0x212) : mword 64) (ITYPE (mword_of_int 8 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ADDI)) pkdb_00878713. Qed.

  Lemma pki_216 : kernel_text -∗ instr (mword_of_int (PK + 0x216) : mword 64) false (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)).
  Proof. mk_base (PK + 0x216)%Z (mword_of_int 0xf8e43423 : mword 32)
    (mword_of_int (PK + 0x216) : mword 64) (STORE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 8), 8)) pkdb_f8e43423. Qed.

  Lemma pki_21a : kernel_text -∗ instr (mword_of_int (PK + 0x21a) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 20), false, 8)).
  Proof. mk_base (PK + 0x21a)%Z (mword_of_int 0x0007ba03 : mword 32)
    (mword_of_int (PK + 0x21a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 20), false, 8)) pkdb_0007ba03. Qed.

  Lemma pki_21e : kernel_text -∗ instr (mword_of_int (PK + 0x21e) : mword 64) false (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ)).
  Proof. mk_base (PK + 0x21e)%Z (mword_of_int 0x000a0d63 : mword 32)
    (mword_of_int (PK + 0x21e) : mword 64) (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ)) pkdb_000a0d63. Qed.

  Lemma pki_222 : kernel_text -∗ instr (mword_of_int (PK + 0x222) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PK + 0x222)%Z (mword_of_int 0x000a4503 : mword 32)
    (mword_of_int (PK + 0x222) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), true, 1)) pkdb_000a4503. Qed.

  Lemma pki_226 : kernel_text -∗ instr (mword_of_int (PK + 0x226) : mword 64) false (BTYPE (mword_of_int 7762 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (PK + 0x226)%Z (mword_of_int 0xe40509e3 : mword 32)
    (mword_of_int (PK + 0x226) : mword 64) (BTYPE (mword_of_int 7762 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BEQ)) pkdb_e40509e3. Qed.

  Lemma pki_22a : kernel_text -∗ instr (mword_of_int (PK + 0x22a) : mword 64) false (JAL (mword_of_int 2095958 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x22a)%Z (mword_of_int 0xb57ff0ef : mword 32)
    (mword_of_int (PK + 0x22a) : mword 64) (JAL (mword_of_int 2095958 : mword 21, Regidx (mword_of_int 1))) pkdb_b57ff0ef. Qed.

  Lemma pki_22e : kernel_text -∗ instr (mword_of_int (PK + 0x22e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_rvc (PK + 0x22e)%Z (mword_of_int 0x0a05 : mword 16)
    (mword_of_int (PK + 0x22e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) pkdc_0a05 exec_execute_C_ADDI. Qed.

  Lemma pki_230 : kernel_text -∗ instr (mword_of_int (PK + 0x230) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), true, 1)).
  Proof. mk_base (PK + 0x230)%Z (mword_of_int 0x000a4503 : mword 32)
    (mword_of_int (PK + 0x230) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), true, 1)) pkdb_000a4503. Qed.

  Lemma pki_234 : kernel_text -∗ instr (mword_of_int (PK + 0x234) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (PK + 0x234)%Z (mword_of_int 0xf97d : mword 16)
    (mword_of_int (PK + 0x234) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) pkdc_f97d exec_execute_C_BNEZ. Qed.

  Lemma pki_236 : kernel_text -∗ instr (mword_of_int (PK + 0x236) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1825 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x236)%Z (mword_of_int 0xb589 : mword 16)
    (mword_of_int (PK + 0x236) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1825 : mword 11) ('b"0")), zreg)) pkdc_b589 exec_execute_C_J. Qed.

  Lemma pki_238 : kernel_text -∗ instr (mword_of_int (PK + 0x238) : mword 64) false (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (PK + 0x238)%Z (mword_of_int 0x00007a17 : mword 32)
    (mword_of_int (PK + 0x238) : mword 64) (UTYPE (mword_of_int 7 : mword 20, Regidx (mword_of_int 20), AUIPC)) pkdb_00007a17. Qed.

  Lemma pki_23c : kernel_text -∗ instr (mword_of_int (PK + 0x23c) : mword 64) false (ITYPE (mword_of_int 2260 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (PK + 0x23c)%Z (mword_of_int 0x8d4a0a13 : mword 32)
    (mword_of_int (PK + 0x23c) : mword 64) (ITYPE (mword_of_int 2260 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) pkdb_8d4a0a13. Qed.

  Lemma pki_240 : kernel_text -∗ instr (mword_of_int (PK + 0x240) : mword 64) false (ITYPE (mword_of_int 40 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x240)%Z (mword_of_int 0x02800513 : mword 32)
    (mword_of_int (PK + 0x240) : mword 64) (ITYPE (mword_of_int 40 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)) pkdb_02800513. Qed.

  Lemma pki_244 : kernel_text -∗ instr (mword_of_int (PK + 0x244) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x244)%Z (mword_of_int 0xb7dd : mword 16)
    (mword_of_int (PK + 0x244) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2035 : mword 11) ('b"0")), zreg)) pkdc_b7dd exec_execute_C_J. Qed.

  Lemma pki_246 : kernel_text -∗ instr (mword_of_int (PK + 0x246) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PK + 0x246)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (PK + 0x246) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) pkdc_8556 exec_execute_C_MV. Qed.

  Lemma pki_248 : kernel_text -∗ instr (mword_of_int (PK + 0x248) : mword 64) false (JAL (mword_of_int 2095928 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x248)%Z (mword_of_int 0xb39ff0ef : mword 32)
    (mword_of_int (PK + 0x248) : mword 64) (JAL (mword_of_int 2095928 : mword 21, Regidx (mword_of_int 1))) pkdb_b39ff0ef. Qed.

  Lemma pki_24c : kernel_text -∗ instr (mword_of_int (PK + 0x24c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x24c)%Z (mword_of_int 0xb535 : mword 16)
    (mword_of_int (PK + 0x24c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1814 : mword 11) ('b"0")), zreg)) pkdc_b535 exec_execute_C_J. Qed.

  Lemma pki_24e : kernel_text -∗ instr (mword_of_int (PK + 0x24e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PK + 0x24e)%Z (mword_of_int 0x74a6 : mword 16)
    (mword_of_int (PK + 0x24e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) pkdc_74a6 exec_execute_C_LDSP. Qed.

  Lemma pki_250 : kernel_text -∗ instr (mword_of_int (PK + 0x250) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PK + 0x250)%Z (mword_of_int 0x69e6 : mword 16)
    (mword_of_int (PK + 0x250) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) pkdc_69e6 exec_execute_C_LDSP. Qed.

  Lemma pki_252 : kernel_text -∗ instr (mword_of_int (PK + 0x252) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PK + 0x252)%Z (mword_of_int 0x6a46 : mword 16)
    (mword_of_int (PK + 0x252) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) pkdc_6a46 exec_execute_C_LDSP. Qed.

  Lemma pki_254 : kernel_text -∗ instr (mword_of_int (PK + 0x254) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (PK + 0x254)%Z (mword_of_int 0x6aa6 : mword 16)
    (mword_of_int (PK + 0x254) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) pkdc_6aa6 exec_execute_C_LDSP. Qed.

  Lemma pki_256 : kernel_text -∗ instr (mword_of_int (PK + 0x256) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PK + 0x256)%Z (mword_of_int 0x6b06 : mword 16)
    (mword_of_int (PK + 0x256) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) pkdc_6b06 exec_execute_C_LDSP. Qed.

  Lemma pki_258 : kernel_text -∗ instr (mword_of_int (PK + 0x258) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PK + 0x258)%Z (mword_of_int 0x7be2 : mword 16)
    (mword_of_int (PK + 0x258) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) pkdc_7be2 exec_execute_C_LDSP. Qed.

  Lemma pki_25a : kernel_text -∗ instr (mword_of_int (PK + 0x25a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PK + 0x25a)%Z (mword_of_int 0x7c42 : mword 16)
    (mword_of_int (PK + 0x25a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) pkdc_7c42 exec_execute_C_LDSP. Qed.

  Lemma pki_25c : kernel_text -∗ instr (mword_of_int (PK + 0x25c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (PK + 0x25c)%Z (mword_of_int 0x7d02 : mword 16)
    (mword_of_int (PK + 0x25c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) pkdc_7d02 exec_execute_C_LDSP. Qed.

  Lemma pki_25e : kernel_text -∗ instr (mword_of_int (PK + 0x25e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)).
  Proof. mk_rvc (PK + 0x25e)%Z (mword_of_int 0x6de2 : mword 16)
    (mword_of_int (PK + 0x25e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)) pkdc_6de2 exec_execute_C_LDSP. Qed.

  Lemma pki_260 : kernel_text -∗ instr (mword_of_int (PK + 0x260) : mword 64) false (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (PK + 0x260)%Z (mword_of_int 0x0000a797 : mword 32)
    (mword_of_int (PK + 0x260) : mword 64) (UTYPE (mword_of_int 10 : mword 20, Regidx (mword_of_int 15), AUIPC)) pkdb_0000a797. Qed.

  Lemma pki_264 : kernel_text -∗ instr (mword_of_int (PK + 0x264) : mword 64) false (LOAD (mword_of_int 2760 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PK + 0x264)%Z (mword_of_int 0xac87a783 : mword 32)
    (mword_of_int (PK + 0x264) : mword 64) (LOAD (mword_of_int 2760 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) pkdb_ac87a783. Qed.

  Lemma pki_268 : kernel_text -∗ instr (mword_of_int (PK + 0x268) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PK + 0x268)%Z (mword_of_int 0xc38d : mword 16)
    (mword_of_int (PK + 0x268) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) pkdc_c38d exec_execute_C_BEQZ. Qed.

  Lemma pki_26a : kernel_text -∗ instr (mword_of_int (PK + 0x26a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (PK + 0x26a)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (PK + 0x26a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma pki_26c : kernel_text -∗ instr (mword_of_int (PK + 0x26c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PK + 0x26c)%Z (mword_of_int 0x70e6 : mword 16)
    (mword_of_int (PK + 0x26c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 15 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) pkdc_70e6 exec_execute_C_LDSP. Qed.

  Lemma pki_26e : kernel_text -∗ instr (mword_of_int (PK + 0x26e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PK + 0x26e)%Z (mword_of_int 0x7446 : mword 16)
    (mword_of_int (PK + 0x26e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 14 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) pkdc_7446 exec_execute_C_LDSP. Qed.

  Lemma pki_270 : kernel_text -∗ instr (mword_of_int (PK + 0x270) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PK + 0x270)%Z (mword_of_int 0x7906 : mword 16)
    (mword_of_int (PK + 0x270) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) pkdc_7906 exec_execute_C_LDSP. Qed.

  Lemma pki_272 : kernel_text -∗ instr (mword_of_int (PK + 0x272) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 12 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PK + 0x272)%Z (mword_of_int 0x6129 : mword 16)
    (mword_of_int (PK + 0x272) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 12 : mword 6), sp, sp, ADDI)) pkdc_6129 exec_execute_C_ADDI16SP. Qed.

  Lemma pki_274 : kernel_text -∗ instr (mword_of_int (PK + 0x274) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PK + 0x274)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PK + 0x274) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma pki_276 : kernel_text -∗ instr (mword_of_int (PK + 0x276) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PK + 0x276)%Z (mword_of_int 0x74a6 : mword 16)
    (mword_of_int (PK + 0x276) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) pkdc_74a6 exec_execute_C_LDSP. Qed.

  Lemma pki_278 : kernel_text -∗ instr (mword_of_int (PK + 0x278) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PK + 0x278)%Z (mword_of_int 0x69e6 : mword 16)
    (mword_of_int (PK + 0x278) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) pkdc_69e6 exec_execute_C_LDSP. Qed.

  Lemma pki_27a : kernel_text -∗ instr (mword_of_int (PK + 0x27a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PK + 0x27a)%Z (mword_of_int 0x6a46 : mword 16)
    (mword_of_int (PK + 0x27a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) pkdc_6a46 exec_execute_C_LDSP. Qed.

  Lemma pki_27c : kernel_text -∗ instr (mword_of_int (PK + 0x27c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (PK + 0x27c)%Z (mword_of_int 0x6aa6 : mword 16)
    (mword_of_int (PK + 0x27c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) pkdc_6aa6 exec_execute_C_LDSP. Qed.

  Lemma pki_27e : kernel_text -∗ instr (mword_of_int (PK + 0x27e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PK + 0x27e)%Z (mword_of_int 0x6b06 : mword 16)
    (mword_of_int (PK + 0x27e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) pkdc_6b06 exec_execute_C_LDSP. Qed.

  Lemma pki_280 : kernel_text -∗ instr (mword_of_int (PK + 0x280) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PK + 0x280)%Z (mword_of_int 0x7be2 : mword 16)
    (mword_of_int (PK + 0x280) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) pkdc_7be2 exec_execute_C_LDSP. Qed.

  Lemma pki_282 : kernel_text -∗ instr (mword_of_int (PK + 0x282) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PK + 0x282)%Z (mword_of_int 0x7c42 : mword 16)
    (mword_of_int (PK + 0x282) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) pkdc_7c42 exec_execute_C_LDSP. Qed.

  Lemma pki_284 : kernel_text -∗ instr (mword_of_int (PK + 0x284) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (PK + 0x284)%Z (mword_of_int 0x7d02 : mword 16)
    (mword_of_int (PK + 0x284) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) pkdc_7d02 exec_execute_C_LDSP. Qed.

  Lemma pki_286 : kernel_text -∗ instr (mword_of_int (PK + 0x286) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)).
  Proof. mk_rvc (PK + 0x286)%Z (mword_of_int 0x6de2 : mword 16)
    (mword_of_int (PK + 0x286) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)) pkdc_6de2 exec_execute_C_LDSP. Qed.

  Lemma pki_288 : kernel_text -∗ instr (mword_of_int (PK + 0x288) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x288)%Z (mword_of_int 0xbfe1 : mword 16)
    (mword_of_int (PK + 0x288) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)) pkdc_bfe1 exec_execute_C_J. Qed.

  Lemma pki_28a : kernel_text -∗ instr (mword_of_int (PK + 0x28a) : mword 64) false (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (PK + 0x28a)%Z (mword_of_int 0x00012517 : mword 32)
    (mword_of_int (PK + 0x28a) : mword 64) (UTYPE (mword_of_int 18 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00012517. Qed.

  Lemma pki_28e : kernel_text -∗ instr (mword_of_int (PK + 0x28e) : mword 64) false (ITYPE (mword_of_int 2930 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x28e)%Z (mword_of_int 0xb7250513 : mword 32)
    (mword_of_int (PK + 0x28e) : mword 64) (ITYPE (mword_of_int 2930 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) pkdb_b7250513. Qed.

  Lemma pki_292 : kernel_text -∗ instr (mword_of_int (PK + 0x292) : mword 64) false (JAL (mword_of_int 1282 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x292)%Z (mword_of_int 0x502000ef : mword 32)
    (mword_of_int (PK + 0x292) : mword 64) (JAL (mword_of_int 1282 : mword 21, Regidx (mword_of_int 1))) pkdb_502000ef. Qed.

  Lemma pki_296 : kernel_text -∗ instr (mword_of_int (PK + 0x296) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x296)%Z (mword_of_int 0xbfd1 : mword 16)
    (mword_of_int (PK + 0x296) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)) pkdc_bfd1 exec_execute_C_J. Qed.

  Lemma pki_298 : kernel_text -∗ instr (mword_of_int (PK + 0x298) : mword 64) false (BTYPE (mword_of_int 7740 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x298)%Z (mword_of_int 0xe37a8ee3 : mword 32)
    (mword_of_int (PK + 0x298) : mword 64) (BTYPE (mword_of_int 7740 : mword 13, Regidx (mword_of_int 23), Regidx (mword_of_int 21), BEQ)) pkdb_e37a8ee3. Qed.

  Lemma pki_29c : kernel_text -∗ instr (mword_of_int (PK + 0x29c) : mword 64) false (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x29c)%Z (mword_of_int 0xf94a8713 : mword 32)
    (mword_of_int (PK + 0x29c) : mword 64) (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)) pkdb_f94a8713. Qed.

  Lemma pki_2a0 : kernel_text -∗ instr (mword_of_int (PK + 0x2a0) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)).
  Proof. mk_base (PK + 0x2a0)%Z (mword_of_int 0x00173713 : mword 32)
    (mword_of_int (PK + 0x2a0) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)) pkdb_00173713. Qed.

  Lemma pki_2a4 : kernel_text -∗ instr (mword_of_int (PK + 0x2a4) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (PK + 0x2a4)%Z (mword_of_int 0x8636 : mword 16)
    (mword_of_int (PK + 0x2a4) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 12), ADD)) pkdc_8636 exec_execute_C_MV. Qed.

  Lemma pki_2a6 : kernel_text -∗ instr (mword_of_int (PK + 0x2a6) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (PK + 0x2a6)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (PK + 0x2a6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  Lemma pki_2a8 : kernel_text -∗ instr (mword_of_int (PK + 0x2a8) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 17 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x2a8)%Z (mword_of_int 0xa00d : mword 16)
    (mword_of_int (PK + 0x2a8) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 17 : mword 11) ('b"0")), zreg)) pkdc_a00d exec_execute_C_J. Qed.

  Lemma pki_2aa : kernel_text -∗ instr (mword_of_int (PK + 0x2aa) : mword 64) false (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (PK + 0x2aa)%Z (mword_of_int 0xf94a8713 : mword 32)
    (mword_of_int (PK + 0x2aa) : mword 64) (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 14), ADDI)) pkdb_f94a8713. Qed.

  Lemma pki_2ae : kernel_text -∗ instr (mword_of_int (PK + 0x2ae) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)).
  Proof. mk_base (PK + 0x2ae)%Z (mword_of_int 0x00173713 : mword 32)
    (mword_of_int (PK + 0x2ae) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), SLTIU)) pkdb_00173713. Qed.

  Lemma pki_2b2 : kernel_text -∗ instr (mword_of_int (PK + 0x2b2) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (PK + 0x2b2)%Z (mword_of_int 0x8656 : mword 16)
    (mword_of_int (PK + 0x2b2) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 12), ADD)) pkdc_8656 exec_execute_C_MV. Qed.

  Lemma pki_2b4 : kernel_text -∗ instr (mword_of_int (PK + 0x2b4) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (PK + 0x2b4)%Z (mword_of_int 0x86d6 : mword 16)
    (mword_of_int (PK + 0x2b4) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 13), ADD)) pkdc_86d6 exec_execute_C_MV. Qed.

  Lemma pki_2b6 : kernel_text -∗ instr (mword_of_int (PK + 0x2b6) : mword 64) false (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PK + 0x2b6)%Z (mword_of_int 0xf9460793 : mword 32)
    (mword_of_int (PK + 0x2b6) : mword 64) (ITYPE (mword_of_int 3988 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 15), ADDI)) pkdb_f9460793. Qed.

  Lemma pki_2ba : kernel_text -∗ instr (mword_of_int (PK + 0x2ba) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTIU)).
  Proof. mk_base (PK + 0x2ba)%Z (mword_of_int 0x0017b793 : mword 32)
    (mword_of_int (PK + 0x2ba) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLTIU)) pkdb_0017b793. Qed.

  Lemma pki_2be : kernel_text -∗ instr (mword_of_int (PK + 0x2be) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), AND)).
  Proof. mk_rvc (PK + 0x2be)%Z (mword_of_int 0x8ff9 : mword 16)
    (mword_of_int (PK + 0x2be) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), AND)) pkdc_8ff9 exec_execute_C_AND. Qed.

  Lemma pki_2c0 : kernel_text -∗ instr (mword_of_int (PK + 0x2c0) : mword 64) false (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PK + 0x2c0)%Z (mword_of_int 0xf9c68593 : mword 32)
    (mword_of_int (PK + 0x2c0) : mword 64) (ITYPE (mword_of_int 3996 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI)) pkdb_f9c68593. Qed.

  Lemma pki_2c4 : kernel_text -∗ instr (mword_of_int (PK + 0x2c4) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)).
  Proof. mk_rvc (PK + 0x2c4)%Z (mword_of_int 0xe199 : mword 16)
    (mword_of_int (PK + 0x2c4) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)) pkdc_e199 exec_execute_C_BNEZ. Qed.

  Lemma pki_2c6 : kernel_text -∗ instr (mword_of_int (PK + 0x2c6) : mword 64) false (BTYPE (mword_of_int 7728 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (PK + 0x2c6)%Z (mword_of_int 0xe20798e3 : mword 32)
    (mword_of_int (PK + 0x2c6) : mword 64) (BTYPE (mword_of_int 7728 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)) pkdb_e20798e3. Qed.

  Lemma pki_2ca : kernel_text -∗ instr (mword_of_int (PK + 0x2ca) : mword 64) false (BTYPE (mword_of_int 7752 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x2ca)%Z (mword_of_int 0xe58a84e3 : mword 32)
    (mword_of_int (PK + 0x2ca) : mword 64) (BTYPE (mword_of_int 7752 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 21), BEQ)) pkdb_e58a84e3. Qed.

  Lemma pki_2ce : kernel_text -∗ instr (mword_of_int (PK + 0x2ce) : mword 64) false (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PK + 0x2ce)%Z (mword_of_int 0xf8b60593 : mword 32)
    (mword_of_int (PK + 0x2ce) : mword 64) (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 11), ADDI)) pkdb_f8b60593. Qed.

  Lemma pki_2d2 : kernel_text -∗ instr (mword_of_int (PK + 0x2d2) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)).
  Proof. mk_rvc (PK + 0x2d2)%Z (mword_of_int 0xe199 : mword 16)
    (mword_of_int (PK + 0x2d2) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)) pkdc_e199 exec_execute_C_BNEZ. Qed.

  Lemma pki_2d4 : kernel_text -∗ instr (mword_of_int (PK + 0x2d4) : mword 64) false (BTYPE (mword_of_int 7768 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (PK + 0x2d4)%Z (mword_of_int 0xe4071ce3 : mword 32)
    (mword_of_int (PK + 0x2d4) : mword 64) (BTYPE (mword_of_int 7768 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE)) pkdb_e4071ce3. Qed.

  Lemma pki_2d8 : kernel_text -∗ instr (mword_of_int (PK + 0x2d8) : mword 64) false (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PK + 0x2d8)%Z (mword_of_int 0xf8b68593 : mword 32)
    (mword_of_int (PK + 0x2d8) : mword 64) (ITYPE (mword_of_int 3979 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 11), ADDI)) pkdb_f8b68593. Qed.

  Lemma pki_2dc : kernel_text -∗ instr (mword_of_int (PK + 0x2dc) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)).
  Proof. mk_rvc (PK + 0x2dc)%Z (mword_of_int 0xe199 : mword 16)
    (mword_of_int (PK + 0x2dc) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)) pkdc_e199 exec_execute_C_BNEZ. Qed.

  Lemma pki_2de : kernel_text -∗ instr (mword_of_int (PK + 0x2de) : mword 64) false (BTYPE (mword_of_int 7786 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (PK + 0x2de)%Z (mword_of_int 0xe60795e3 : mword 32)
    (mword_of_int (PK + 0x2de) : mword 64) (BTYPE (mword_of_int 7786 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)) pkdb_e60795e3. Qed.

  Lemma pki_2e2 : kernel_text -∗ instr (mword_of_int (PK + 0x2e2) : mword 64) false (BTYPE (mword_of_int 7810 : mword 13, Regidx (mword_of_int 26), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x2e2)%Z (mword_of_int 0xe9aa81e3 : mword 32)
    (mword_of_int (PK + 0x2e2) : mword 64) (BTYPE (mword_of_int 7810 : mword 13, Regidx (mword_of_int 26), Regidx (mword_of_int 21), BEQ)) pkdb_e9aa81e3. Qed.

  Lemma pki_2e6 : kernel_text -∗ instr (mword_of_int (PK + 0x2e6) : mword 64) false (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (PK + 0x2e6)%Z (mword_of_int 0xf8860613 : mword 32)
    (mword_of_int (PK + 0x2e6) : mword 64) (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) pkdb_f8860613. Qed.

  Lemma pki_2ea : kernel_text -∗ instr (mword_of_int (PK + 0x2ea) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BNE)).
  Proof. mk_rvc (PK + 0x2ea)%Z (mword_of_int 0xe219 : mword 16)
    (mword_of_int (PK + 0x2ea) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BNE)) pkdc_e219 exec_execute_C_BNEZ. Qed.

  Lemma pki_2ec : kernel_text -∗ instr (mword_of_int (PK + 0x2ec) : mword 64) false (BTYPE (mword_of_int 7826 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (PK + 0x2ec)%Z (mword_of_int 0xe80719e3 : mword 32)
    (mword_of_int (PK + 0x2ec) : mword 64) (BTYPE (mword_of_int 7826 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 14), BNE)) pkdb_e80719e3. Qed.

  Lemma pki_2f0 : kernel_text -∗ instr (mword_of_int (PK + 0x2f0) : mword 64) false (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).
  Proof. mk_base (PK + 0x2f0)%Z (mword_of_int 0xf8868693 : mword 32)
    (mword_of_int (PK + 0x2f0) : mword 64) (ITYPE (mword_of_int 3976 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) pkdb_f8868693. Qed.

  Lemma pki_2f4 : kernel_text -∗ instr (mword_of_int (PK + 0x2f4) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BNE)).
  Proof. mk_rvc (PK + 0x2f4)%Z (mword_of_int 0xe299 : mword 16)
    (mword_of_int (PK + 0x2f4) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BNE)) pkdc_e299 exec_execute_C_BNEZ. Qed.

  Lemma pki_2f6 : kernel_text -∗ instr (mword_of_int (PK + 0x2f6) : mword 64) false (BTYPE (mword_of_int 7842 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (PK + 0x2f6)%Z (mword_of_int 0xea0791e3 : mword 32)
    (mword_of_int (PK + 0x2f6) : mword 64) (BTYPE (mword_of_int 7842 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BNE)) pkdb_ea0791e3. Qed.

  Lemma pki_2fa : kernel_text -∗ instr (mword_of_int (PK + 0x2fa) : mword 64) false (BTYPE (mword_of_int 7866 : mword 13, Regidx (mword_of_int 27), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x2fa)%Z (mword_of_int 0xebba8de3 : mword 32)
    (mword_of_int (PK + 0x2fa) : mword 64) (BTYPE (mword_of_int 7866 : mword 13, Regidx (mword_of_int 27), Regidx (mword_of_int 21), BEQ)) pkdb_ebba8de3. Qed.

  Lemma pki_2fe : kernel_text -∗ instr (mword_of_int (PK + 0x2fe) : mword 64) false (ITYPE (mword_of_int 99 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PK + 0x2fe)%Z (mword_of_int 0x06300793 : mword 32)
    (mword_of_int (PK + 0x2fe) : mword 64) (ITYPE (mword_of_int 99 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)) pkdb_06300793. Qed.

  Lemma pki_302 : kernel_text -∗ instr (mword_of_int (PK + 0x302) : mword 64) false (BTYPE (mword_of_int 7928 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x302)%Z (mword_of_int 0xeefa8ce3 : mword 32)
    (mword_of_int (PK + 0x302) : mword 64) (BTYPE (mword_of_int 7928 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)) pkdb_eefa8ce3. Qed.

  Lemma pki_306 : kernel_text -∗ instr (mword_of_int (PK + 0x306) : mword 64) false (ITYPE (mword_of_int 115 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PK + 0x306)%Z (mword_of_int 0x07300793 : mword 32)
    (mword_of_int (PK + 0x306) : mword 64) (ITYPE (mword_of_int 115 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)) pkdb_07300793. Qed.

  Lemma pki_30a : kernel_text -∗ instr (mword_of_int (PK + 0x30a) : mword 64) false (BTYPE (mword_of_int 7940 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x30a)%Z (mword_of_int 0xf0fa82e3 : mword 32)
    (mword_of_int (PK + 0x30a) : mword 64) (BTYPE (mword_of_int 7940 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)) pkdb_f0fa82e3. Qed.

  Lemma pki_30e : kernel_text -∗ instr (mword_of_int (PK + 0x30e) : mword 64) false (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (PK + 0x30e)%Z (mword_of_int 0x02500793 : mword 32)
    (mword_of_int (PK + 0x30e) : mword 64) (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 15), ADDI)) pkdb_02500793. Qed.

  Lemma pki_312 : kernel_text -∗ instr (mword_of_int (PK + 0x312) : mword 64) false (BTYPE (mword_of_int 7988 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x312)%Z (mword_of_int 0xf2fa8ae3 : mword 32)
    (mword_of_int (PK + 0x312) : mword 64) (BTYPE (mword_of_int 7988 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 21), BEQ)) pkdb_f2fa8ae3. Qed.

  Lemma pki_316 : kernel_text -∗ instr (mword_of_int (PK + 0x316) : mword 64) false (BTYPE (mword_of_int 8032 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (PK + 0x316)%Z (mword_of_int 0xf60a80e3 : mword 32)
    (mword_of_int (PK + 0x316) : mword 64) (BTYPE (mword_of_int 8032 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)) pkdb_f60a80e3. Qed.

  Lemma pki_31a : kernel_text -∗ instr (mword_of_int (PK + 0x31a) : mword 64) false (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PK + 0x31a)%Z (mword_of_int 0x02500513 : mword 32)
    (mword_of_int (PK + 0x31a) : mword 64) (ITYPE (mword_of_int 37 : mword 12, zreg, Regidx (mword_of_int 10), ADDI)) pkdb_02500513. Qed.

  Lemma pki_31e : kernel_text -∗ instr (mword_of_int (PK + 0x31e) : mword 64) false (JAL (mword_of_int 2095714 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x31e)%Z (mword_of_int 0xa63ff0ef : mword 32)
    (mword_of_int (PK + 0x31e) : mword 64) (JAL (mword_of_int 2095714 : mword 21, Regidx (mword_of_int 1))) pkdb_a63ff0ef. Qed.

  Lemma pki_322 : kernel_text -∗ instr (mword_of_int (PK + 0x322) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PK + 0x322)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (PK + 0x322) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) pkdc_8556 exec_execute_C_MV. Qed.

  Lemma pki_324 : kernel_text -∗ instr (mword_of_int (PK + 0x324) : mword 64) false (JAL (mword_of_int 2095708 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PK + 0x324)%Z (mword_of_int 0xa5dff0ef : mword 32)
    (mword_of_int (PK + 0x324) : mword 64) (JAL (mword_of_int 2095708 : mword 21, Regidx (mword_of_int 1))) pkdb_a5dff0ef. Qed.

  Lemma pki_328 : kernel_text -∗ instr (mword_of_int (PK + 0x328) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PK + 0x328)%Z (mword_of_int 0xbb81 : mword 16)
    (mword_of_int (PK + 0x328) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1704 : mword 11) ('b"0")), zreg)) pkdc_bb81 exec_execute_C_J. Qed.


End WpPrintkDecode.

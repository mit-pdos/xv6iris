(* CodePipealloc.v -- the instruction-DECODE layer for xv6's pipealloc().
   For EVERY instruction of

     pipealloc @ 0x80004378 .. 0x8000443e   (offsets 0x00 .. 0xc6)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pai_<off>]) plus
   the per-instruction decode facts they consume.  Same shape as
   CodeFilealloc / CodeKalloc: [mk_rvc] for compressed instructions,
   [mk_base] for 4-byte ones.

   pipealloc's frame is the 48-byte one (c.addi16sp sp,-48 -- NOT a c.addi --
   with six spill/reload slots), and every one of those words plus c.mv s1,a0,
   c.li a0,0 and c.jr ra already lives in KernelRvcDecode as [cdec_<word>];
   only the words nothing else uses are local, keyed by bits in the same way.

   Body (all instruction bytes from the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/pipe.c):

     0x00 7179       c.addi16sp sp,-48
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 ec26       c.sdsp s1,24(sp)
     0x08 e052       c.sdsp s4,0(sp)
     0x0a 1800       c.addi4spn s0,sp,48
     0x0c 84aa       c.mv  s1,a0          # s1 := f0
     0x0e 8a2e       c.mv  s4,a1          # s4 := f1
     0x10 0005b023   sd    zero,0(a1)     # *f1 = 0
     0x14 00053023   sd    zero,0(a0)     # *f0 = 0
     0x18 c29ff0ef   jal   ra,filealloc
     0x1c e088       c.sd  a0,0(s1)       # *f0 = filealloc()
     0x1e c549       c.beqz a0,+0x8a      # -> 0xa8, no file
     0x20 c21ff0ef   jal   ra,filealloc
     0x24 00aa3023   sd    a0,0(s4)       # *f1 = filealloc()
     0x28 cd25       c.beqz a0,+0x78      # -> 0xa0, no file
     0x2a e84a       c.sdsp s2,16(sp)
     0x2c f8afc0ef   jal   ra,kalloc
     0x30 892a       c.mv  s2,a0          # s2 := pi
     0x32 c12d       c.beqz a0,+0x62      # -> 0x94, no page
     0x34 e44e       c.sdsp s3,8(sp)
     0x36 4985       c.li  s3,1
     0x38 23352023   sw    s3,544(a0)     # pi->readopen  = 1
     0x3c 23352223   sw    s3,548(a0)     # pi->writeopen = 1
     0x40 20052e23   sw    zero,540(a0)   # pi->nwrite = 0
     0x44 20052c23   sw    zero,536(a0)   # pi->nread  = 0
     0x48 00003597   auipc a1,0x3
     0x4c 1d858593   addi  a1,a1,472      # a1 := "pipe"
     0x50 fc0fc0ef   jal   ra,initlock
     0x54 609c       c.ld  a5,0(s1)
     0x56 0137a023   sw    s3,0(a5)       # f0->type = FD_PIPE
     0x5a 609c       c.ld  a5,0(s1)
     0x5c 01378423   sb    s3,8(a5)       # f0->readable = 1
     0x60 609c       c.ld  a5,0(s1)
     0x62 000784a3   sb    zero,9(a5)     # f0->writable = 0
     0x66 609c       c.ld  a5,0(s1)
     0x68 0127b823   sd    s2,16(a5)      # f0->pipe = pi
     0x6c 000a3783   ld    a5,0(s4)
     0x70 0137a023   sw    s3,0(a5)       # f1->type = FD_PIPE
     0x74 000a3783   ld    a5,0(s4)
     0x78 00078423   sb    zero,8(a5)     # f1->readable = 0
     0x7c 000a3783   ld    a5,0(s4)
     0x80 013784a3   sb    s3,9(a5)       # f1->writable = 1
     0x84 000a3783   ld    a5,0(s4)
     0x88 0127b823   sd    s2,16(a5)      # f1->pipe = pi
     0x8c 4501       c.li  a0,0           # return 0
     0x8e 6942       c.ldsp s2,16(sp)
     0x90 69a2       c.ldsp s3,8(sp)
     0x92 a01d       c.j   +0x26          # -> 0xb8
     0x94 6088       c.ld  a0,0(s1)                             <- NO PAGE
     0x96 c119       c.beqz a0,+0x06      # -> 0x9c  (dead: *f0 != 0)
     0x98 6942       c.ldsp s2,16(sp)
     0x9a a029       c.j   +0x0a          # -> 0xa4
     0x9c 6942       c.ldsp s2,16(sp)                           <- dead
     0x9e a029       c.j   +0x0a          # -> 0xa8
     0xa0 6088       c.ld  a0,0(s1)                             <- NO SECOND FILE
     0xa2 c10d       c.beqz a0,+0x22      # -> 0xc4  (dead: *f0 != 0)
     0xa4 c41ff0ef   jal   ra,fileclose   # fileclose( *f0)
     0xa8 000a3783   ld    a5,0(s4)
     0xac 557d       c.li  a0,-1
     0xae c789       c.beqz a5,+0x0a      # -> 0xb8, *f1 was never taken
     0xb0 853e       c.mv  a0,a5
     0xb2 c33ff0ef   jal   ra,fileclose   # fileclose( *f1)
     0xb6 557d       c.li  a0,-1
     0xb8 70a2       c.ldsp ra,40(sp)                           <- EPILOGUE
     0xba 7402       c.ldsp s0,32(sp)
     0xbc 64e2       c.ldsp s1,24(sp)
     0xbe 6a02       c.ldsp s4,0(sp)
     0xc0 6145       c.addi16sp sp,48
     0xc2 8082       c.ret
     0xc4 557d       c.li  a0,-1                                <- dead
     0xc6 bfcd       c.j   -0x0e          # -> 0xb8                        *)
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
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for the words no other function uses.          *)
(* ===================================================================== *)

(* 0x8a2e  c.mv s4,a1 -- [cdec_8a2e] (KernelRvcDecode.v) *)

(* 0xe088  c.sd a0,0(s1) -- shared with argaddr, so [cdec_e088] /
   [cexec_sd0_s1_a0] (KernelRvcDecode.v) *)

(* 0xc549  c.beqz a0,+0x8a *)
Lemma padc_c549 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc549 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 69, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcd25  c.beqz a0,+0x78 *)
Lemma padc_cd25 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd25 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 60, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x892a  c.mv s2,a0 *)
(* [cdec_892a] -- shared, see KernelRvcDecode.v *)

(* 0xc12d  c.beqz a0,+0x62 *)
Lemma padc_c12d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc12d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 49, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4985  c.li s3,1 *)
Lemma padc_4985 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4985 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0xa01d  c.j +0x26 *)
Lemma padc_a01d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa01d : mword 16)) s
  = Some (C_J (mword_of_int 19), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0xc119  c.beqz a0,+0x06 -- [cdec_c119] (KernelRvcDecode.v) *)

(* 0xa029  c.j +0x0a *)
Lemma padc_a029 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa029 : mword 16)) s
  = Some (C_J (mword_of_int 5), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc10d  c.beqz a0,+0x22 *)
Lemma padc_c10d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc10d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 17, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x557d  c.li a0,-1 *)

(* 0xc789  c.beqz a5,+0x0a *)
Lemma padc_c789 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc789 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 5, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x853e  c.mv a0,a5 -- [cdec_853e] (KernelRvcDecode.v) *)

(* 0xbfcd  c.j -0x0e *)

(* the three compressed reg-base memory ops, in the leaf-friendly (Regidx /
   literal-immediate) form: instances of WpMmodeLeafBase's
   [exec_execute_C_{LD,SD}_leaf]. *)
Lemma paexec_ld0_a5 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma paexec_ld0_a0 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.


(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0x0005b023  sd zero,0(a1) *)
Lemma padb_0005b023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0005b023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 11), 8), s).
Proof. decode_bridge_ms. Qed.


(* 0x00aa3023  sd a0,0(s4) *)
Lemma padb_00aa3023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00aa3023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 20), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x23352023  sw s3,544(a0) *)
Lemma padb_23352023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x23352023 : mword 32)) s
  = Some (STORE (mword_of_int 544 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x23352223  sw s3,548(a0) *)
Lemma padb_23352223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x23352223 : mword 32)) s
  = Some (STORE (mword_of_int 548 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x20052e23  sw zero,540(a0) *)
Lemma padb_20052e23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x20052e23 : mword 32)) s
  = Some (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x20052c23  sw zero,536(a0) *)
Lemma padb_20052c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x20052c23 : mword 32)) s
  = Some (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x0137a023  sw s3,0(a5) *)
Lemma padb_0137a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0137a023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x01378423  sb s3,8(a5) *)
Lemma padb_01378423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01378423 : mword 32)) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x000784a3  sb zero,9(a5) *)
Lemma padb_000784a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000784a3 : mword 32)) s
  = Some (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x0127b823  sd s2,16(a5) *)
Lemma padb_0127b823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0127b823 : mword 32)) s
  = Some (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x00078423  sb zero,8(a5) *)
Lemma padb_00078423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00078423 : mword 32)) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x013784a3  sb s3,9(a5) *)
Lemma padb_013784a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x013784a3 : mword 32)) s
  = Some (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x000a3783  ld a5,0(s4) *)
Lemma padb_000a3783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000a3783 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8), s).
Proof. decode_bridge_ms. Qed.


(* 0x1d858593  addi a1,a1,472 *)
Lemma padb_1d858593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1d858593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x1d8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xc29ff0ef  jal ra,filealloc *)
Lemma padb_c29ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc29ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1ffc28 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xc21ff0ef  jal ra,filealloc *)
Lemma padb_c21ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc21ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1ffc20 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xf8afc0ef  jal ra,kalloc *)
Lemma padb_f8afc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf8afc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fc78a : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfc0fc0ef  jal ra,initlock *)
Lemma padb_fc0fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc0fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fc7c0 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xc41ff0ef  jal ra,fileclose *)
Lemma padb_c41ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc41ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1ffc40 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xc33ff0ef  jal ra,fileclose *)
Lemma padb_c33ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc33ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1ffc32 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.
(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section PipeallocInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation PA := KernelSyms.pipealloc.

  (* +0x00  7179  c.addi16sp sp,-48 *)
  Lemma pai_00 : kernel_text -∗ instr (mword_of_int (PA + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PA + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (PA + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  (* +0x02  f406  c.sdsp ra,40(sp) *)
  Lemma pai_02 : kernel_text -∗ instr (mword_of_int (PA + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PA + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (PA + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  (* +0x04  f022  c.sdsp s0,32(sp) *)
  Lemma pai_04 : kernel_text -∗ instr (mword_of_int (PA + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PA + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (PA + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  (* +0x06  ec26  c.sdsp s1,24(sp) *)
  Lemma pai_06 : kernel_text -∗ instr (mword_of_int (PA + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PA + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (PA + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  (* +0x08  e052  c.sdsp s4,0(sp) *)
  Lemma pai_08 : kernel_text -∗ instr (mword_of_int (PA + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (PA + 0x08)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (PA + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  (* +0x0a  1800  c.addi4spn s0,sp,48 *)
  Lemma pai_0a : kernel_text -∗ instr (mword_of_int (PA + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PA + 0x0a)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (PA + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* +0x0c  84aa  c.mv s1,a0 *)
  Lemma pai_0c : kernel_text -∗ instr (mword_of_int (PA + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PA + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (PA + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* +0x0e  8a2e  c.mv s4,a1 *)
  Lemma pai_0e : kernel_text -∗ instr (mword_of_int (PA + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (PA + 0x0e)%Z (mword_of_int 0x8a2e : mword 16)
    (mword_of_int (PA + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2e exec_execute_C_MV. Qed.

  (* +0x10  0005b023  sd zero,0(a1) *)
  Lemma pai_10 : kernel_text -∗ instr (mword_of_int (PA + 0x10) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 11), 8)).
  Proof. mk_base (PA + 0x10)%Z (mword_of_int 0x0005b023 : mword 32)
    (mword_of_int (PA + 0x10) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 11), 8)) padb_0005b023. Qed.

  (* +0x14  00053023  sd zero,0(a0) *)
  Lemma pai_14 : kernel_text -∗ instr (mword_of_int (PA + 0x14) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (PA + 0x14)%Z (mword_of_int 0x00053023 : mword 32)
    (mword_of_int (PA + 0x14) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)) bdec_00053023. Qed.

  (* +0x18  c29ff0ef  jal ra,filealloc *)
  Lemma pai_18 : kernel_text -∗ instr (mword_of_int (PA + 0x18) : mword 64) false (JAL (mword_of_int 0x1ffc28 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0x18)%Z (mword_of_int 0xc29ff0ef : mword 32)
    (mword_of_int (PA + 0x18) : mword 64) (JAL (mword_of_int 0x1ffc28 : mword 21, Regidx (mword_of_int 1))) padb_c29ff0ef. Qed.

  (* +0x1c  e088  c.sd a0,0(s1) *)
  Lemma pai_1c : kernel_text -∗ instr (mword_of_int (PA + 0x1c) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (PA + 0x1c)%Z (mword_of_int 0xe088 : mword 16)
    (mword_of_int (PA + 0x1c) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) cdec_e088 cexec_sd0_s1_a0. Qed.

  (* +0x1e  c549  c.beqz a0,+0x8a *)
  Lemma pai_1e : kernel_text -∗ instr (mword_of_int (PA + 0x1e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 69 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_rvc (PA + 0x1e)%Z (mword_of_int 0xc549 : mword 16)
    (mword_of_int (PA + 0x1e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 69 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)) padc_c549 exec_execute_C_BEQZ. Qed.

  (* +0x20  c21ff0ef  jal ra,filealloc *)
  Lemma pai_20 : kernel_text -∗ instr (mword_of_int (PA + 0x20) : mword 64) false (JAL (mword_of_int 0x1ffc20 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0x20)%Z (mword_of_int 0xc21ff0ef : mword 32)
    (mword_of_int (PA + 0x20) : mword 64) (JAL (mword_of_int 0x1ffc20 : mword 21, Regidx (mword_of_int 1))) padb_c21ff0ef. Qed.

  (* +0x24  00aa3023  sd a0,0(s4) *)
  Lemma pai_24 : kernel_text -∗ instr (mword_of_int (PA + 0x24) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 20), 8)).
  Proof. mk_base (PA + 0x24)%Z (mword_of_int 0x00aa3023 : mword 32)
    (mword_of_int (PA + 0x24) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 20), 8)) padb_00aa3023. Qed.

  (* +0x28  cd25  c.beqz a0,+0x78 *)
  Lemma pai_28 : kernel_text -∗ instr (mword_of_int (PA + 0x28) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 60 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_rvc (PA + 0x28)%Z (mword_of_int 0xcd25 : mword 16)
    (mword_of_int (PA + 0x28) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 60 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)) padc_cd25 exec_execute_C_BEQZ. Qed.

  (* +0x2a  e84a  c.sdsp s2,16(sp) *)
  Lemma pai_2a : kernel_text -∗ instr (mword_of_int (PA + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PA + 0x2a)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (PA + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  (* +0x2c  f8afc0ef  jal ra,kalloc *)
  Lemma pai_2c : kernel_text -∗ instr (mword_of_int (PA + 0x2c) : mword 64) false (JAL (mword_of_int 0x1fc78a : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0x2c)%Z (mword_of_int 0xf8afc0ef : mword 32)
    (mword_of_int (PA + 0x2c) : mword 64) (JAL (mword_of_int 0x1fc78a : mword 21, Regidx (mword_of_int 1))) padb_f8afc0ef. Qed.

  (* +0x30  892a  c.mv s2,a0 *)
  Lemma pai_30 : kernel_text -∗ instr (mword_of_int (PA + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PA + 0x30)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (PA + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  (* +0x32  c12d  c.beqz a0,+0x62 *)
  Lemma pai_32 : kernel_text -∗ instr (mword_of_int (PA + 0x32) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 49 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_rvc (PA + 0x32)%Z (mword_of_int 0xc12d : mword 16)
    (mword_of_int (PA + 0x32) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 49 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)) padc_c12d exec_execute_C_BEQZ. Qed.

  (* +0x34  e44e  c.sdsp s3,8(sp) *)
  Lemma pai_34 : kernel_text -∗ instr (mword_of_int (PA + 0x34) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (PA + 0x34)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (PA + 0x34) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  (* +0x36  4985  c.li s3,1 *)
  Lemma pai_36 : kernel_text -∗ instr (mword_of_int (PA + 0x36) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (PA + 0x36)%Z (mword_of_int 0x4985 : mword 16)
    (mword_of_int (PA + 0x36) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) padc_4985 exec_execute_C_LI. Qed.

  (* +0x38  23352023  sw s3,544(a0) *)
  Lemma pai_38 : kernel_text -∗ instr (mword_of_int (PA + 0x38) : mword 64) false (STORE (mword_of_int 544 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (PA + 0x38)%Z (mword_of_int 0x23352023 : mword 32)
    (mword_of_int (PA + 0x38) : mword 64) (STORE (mword_of_int 544 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4)) padb_23352023. Qed.

  (* +0x3c  23352223  sw s3,548(a0) *)
  Lemma pai_3c : kernel_text -∗ instr (mword_of_int (PA + 0x3c) : mword 64) false (STORE (mword_of_int 548 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (PA + 0x3c)%Z (mword_of_int 0x23352223 : mword 32)
    (mword_of_int (PA + 0x3c) : mword 64) (STORE (mword_of_int 548 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), 4)) padb_23352223. Qed.

  (* +0x40  20052e23  sw zero,540(a0) *)
  Lemma pai_40 : kernel_text -∗ instr (mword_of_int (PA + 0x40) : mword 64) false (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (PA + 0x40)%Z (mword_of_int 0x20052e23 : mword 32)
    (mword_of_int (PA + 0x40) : mword 64) (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)) padb_20052e23. Qed.

  (* +0x44  20052c23  sw zero,536(a0) *)
  Lemma pai_44 : kernel_text -∗ instr (mword_of_int (PA + 0x44) : mword 64) false (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (PA + 0x44)%Z (mword_of_int 0x20052c23 : mword 32)
    (mword_of_int (PA + 0x44) : mword 64) (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)) padb_20052c23. Qed.

  (* +0x48  00003597  auipc a1,0x3 *)
  Lemma pai_48 : kernel_text -∗ instr (mword_of_int (PA + 0x48) : mword 64) false (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (PA + 0x48)%Z (mword_of_int 0x00003597 : mword 32)
    (mword_of_int (PA + 0x48) : mword 64) (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 11), AUIPC)) bdec_00003597. Qed.

  (* +0x4c  1d858593  addi a1,a1,472 *)
  Lemma pai_4c : kernel_text -∗ instr (mword_of_int (PA + 0x4c) : mword 64) false (ITYPE (mword_of_int 0x1d8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (PA + 0x4c)%Z (mword_of_int 0x1d858593 : mword 32)
    (mword_of_int (PA + 0x4c) : mword 64) (ITYPE (mword_of_int 0x1d8 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) padb_1d858593. Qed.

  (* +0x50  fc0fc0ef  jal ra,initlock *)
  Lemma pai_50 : kernel_text -∗ instr (mword_of_int (PA + 0x50) : mword 64) false (JAL (mword_of_int 0x1fc7c0 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0x50)%Z (mword_of_int 0xfc0fc0ef : mword 32)
    (mword_of_int (PA + 0x50) : mword 64) (JAL (mword_of_int 0x1fc7c0 : mword 21, Regidx (mword_of_int 1))) padb_fc0fc0ef. Qed.

  (* +0x54  609c  c.ld a5,0(s1) *)
  Lemma pai_54 : kernel_text -∗ instr (mword_of_int (PA + 0x54) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (PA + 0x54)%Z (mword_of_int 0x609c : mword 16)
    (mword_of_int (PA + 0x54) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) cdec_609c paexec_ld0_a5. Qed.

  (* +0x56  0137a023  sw s3,0(a5) *)
  Lemma pai_56 : kernel_text -∗ instr (mword_of_int (PA + 0x56) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (PA + 0x56)%Z (mword_of_int 0x0137a023 : mword 32)
    (mword_of_int (PA + 0x56) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 4)) padb_0137a023. Qed.

  (* +0x5a  609c  c.ld a5,0(s1) *)
  Lemma pai_5a : kernel_text -∗ instr (mword_of_int (PA + 0x5a) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (PA + 0x5a)%Z (mword_of_int 0x609c : mword 16)
    (mword_of_int (PA + 0x5a) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) cdec_609c paexec_ld0_a5. Qed.

  (* +0x5c  01378423  sb s3,8(a5) *)
  Lemma pai_5c : kernel_text -∗ instr (mword_of_int (PA + 0x5c) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (PA + 0x5c)%Z (mword_of_int 0x01378423 : mword 32)
    (mword_of_int (PA + 0x5c) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1)) padb_01378423. Qed.

  (* +0x60  609c  c.ld a5,0(s1) *)
  Lemma pai_60 : kernel_text -∗ instr (mword_of_int (PA + 0x60) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (PA + 0x60)%Z (mword_of_int 0x609c : mword 16)
    (mword_of_int (PA + 0x60) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) cdec_609c paexec_ld0_a5. Qed.

  (* +0x62  000784a3  sb zero,9(a5) *)
  Lemma pai_62 : kernel_text -∗ instr (mword_of_int (PA + 0x62) : mword 64) false (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (PA + 0x62)%Z (mword_of_int 0x000784a3 : mword 32)
    (mword_of_int (PA + 0x62) : mword 64) (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)) padb_000784a3. Qed.

  (* +0x66  609c  c.ld a5,0(s1) *)
  Lemma pai_66 : kernel_text -∗ instr (mword_of_int (PA + 0x66) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (PA + 0x66)%Z (mword_of_int 0x609c : mword 16)
    (mword_of_int (PA + 0x66) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) cdec_609c paexec_ld0_a5. Qed.

  (* +0x68  0127b823  sd s2,16(a5) *)
  Lemma pai_68 : kernel_text -∗ instr (mword_of_int (PA + 0x68) : mword 64) false (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (PA + 0x68)%Z (mword_of_int 0x0127b823 : mword 32)
    (mword_of_int (PA + 0x68) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), 8)) padb_0127b823. Qed.

  (* +0x6c  000a3783  ld a5,0(s4) *)
  Lemma pai_6c : kernel_text -∗ instr (mword_of_int (PA + 0x6c) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PA + 0x6c)%Z (mword_of_int 0x000a3783 : mword 32)
    (mword_of_int (PA + 0x6c) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)) padb_000a3783. Qed.

  (* +0x70  0137a023  sw s3,0(a5) *)
  Lemma pai_70 : kernel_text -∗ instr (mword_of_int (PA + 0x70) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (PA + 0x70)%Z (mword_of_int 0x0137a023 : mword 32)
    (mword_of_int (PA + 0x70) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 4)) padb_0137a023. Qed.

  (* +0x74  000a3783  ld a5,0(s4) *)
  Lemma pai_74 : kernel_text -∗ instr (mword_of_int (PA + 0x74) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PA + 0x74)%Z (mword_of_int 0x000a3783 : mword 32)
    (mword_of_int (PA + 0x74) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)) padb_000a3783. Qed.

  (* +0x78  00078423  sb zero,8(a5) *)
  Lemma pai_78 : kernel_text -∗ instr (mword_of_int (PA + 0x78) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (PA + 0x78)%Z (mword_of_int 0x00078423 : mword 32)
    (mword_of_int (PA + 0x78) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)) padb_00078423. Qed.

  (* +0x7c  000a3783  ld a5,0(s4) *)
  Lemma pai_7c : kernel_text -∗ instr (mword_of_int (PA + 0x7c) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PA + 0x7c)%Z (mword_of_int 0x000a3783 : mword 32)
    (mword_of_int (PA + 0x7c) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)) padb_000a3783. Qed.

  (* +0x80  013784a3  sb s3,9(a5) *)
  Lemma pai_80 : kernel_text -∗ instr (mword_of_int (PA + 0x80) : mword 64) false (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (PA + 0x80)%Z (mword_of_int 0x013784a3 : mword 32)
    (mword_of_int (PA + 0x80) : mword 64) (STORE (mword_of_int 9 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), 1)) padb_013784a3. Qed.

  (* +0x84  000a3783  ld a5,0(s4) *)
  Lemma pai_84 : kernel_text -∗ instr (mword_of_int (PA + 0x84) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PA + 0x84)%Z (mword_of_int 0x000a3783 : mword 32)
    (mword_of_int (PA + 0x84) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)) padb_000a3783. Qed.

  (* +0x88  0127b823  sd s2,16(a5) *)
  Lemma pai_88 : kernel_text -∗ instr (mword_of_int (PA + 0x88) : mword 64) false (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), 8)).
  Proof. mk_base (PA + 0x88)%Z (mword_of_int 0x0127b823 : mword 32)
    (mword_of_int (PA + 0x88) : mword 64) (STORE (mword_of_int 16 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), 8)) padb_0127b823. Qed.

  (* +0x8c  4501  c.li a0,0 *)
  Lemma pai_8c : kernel_text -∗ instr (mword_of_int (PA + 0x8c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (PA + 0x8c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (PA + 0x8c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* +0x8e  6942  c.ldsp s2,16(sp) *)
  Lemma pai_8e : kernel_text -∗ instr (mword_of_int (PA + 0x8e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PA + 0x8e)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (PA + 0x8e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  (* +0x90  69a2  c.ldsp s3,8(sp) *)
  Lemma pai_90 : kernel_text -∗ instr (mword_of_int (PA + 0x90) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PA + 0x90)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (PA + 0x90) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  (* +0x92  a01d  c.j +0x26 *)
  Lemma pai_92 : kernel_text -∗ instr (mword_of_int (PA + 0x92) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 19 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PA + 0x92)%Z (mword_of_int 0xa01d : mword 16)
    (mword_of_int (PA + 0x92) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 19 : mword 11) ('b"0")), zreg)) padc_a01d exec_execute_C_J. Qed.

  (* +0x94  6088  c.ld a0,0(s1) *)
  Lemma pai_94 : kernel_text -∗ instr (mword_of_int (PA + 0x94) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (PA + 0x94)%Z (mword_of_int 0x6088 : mword 16)
    (mword_of_int (PA + 0x94) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)) cdec_6088 paexec_ld0_a0. Qed.

  (* +0x96  c119  c.beqz a0,+0x06 *)
  Lemma pai_96 : kernel_text -∗ instr (mword_of_int (PA + 0x96) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_rvc (PA + 0x96)%Z (mword_of_int 0xc119 : mword 16)
    (mword_of_int (PA + 0x96) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)) cdec_c119 exec_execute_C_BEQZ. Qed.

  (* +0x98  6942  c.ldsp s2,16(sp) *)
  Lemma pai_98 : kernel_text -∗ instr (mword_of_int (PA + 0x98) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PA + 0x98)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (PA + 0x98) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  (* +0x9a  a029  c.j +0x0a *)
  Lemma pai_9a : kernel_text -∗ instr (mword_of_int (PA + 0x9a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PA + 0x9a)%Z (mword_of_int 0xa029 : mword 16)
    (mword_of_int (PA + 0x9a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)) padc_a029 exec_execute_C_J. Qed.

  (* +0x9c  6942  c.ldsp s2,16(sp) *)
  Lemma pai_9c : kernel_text -∗ instr (mword_of_int (PA + 0x9c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PA + 0x9c)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (PA + 0x9c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  (* +0x9e  a029  c.j +0x0a *)
  Lemma pai_9e : kernel_text -∗ instr (mword_of_int (PA + 0x9e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PA + 0x9e)%Z (mword_of_int 0xa029 : mword 16)
    (mword_of_int (PA + 0x9e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)) padc_a029 exec_execute_C_J. Qed.

  (* +0xa0  6088  c.ld a0,0(s1) *)
  Lemma pai_a0 : kernel_text -∗ instr (mword_of_int (PA + 0xa0) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (PA + 0xa0)%Z (mword_of_int 0x6088 : mword 16)
    (mword_of_int (PA + 0xa0) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), false, 8)) cdec_6088 paexec_ld0_a0. Qed.

  (* +0xa2  c10d  c.beqz a0,+0x22 *)
  Lemma pai_a2 : kernel_text -∗ instr (mword_of_int (PA + 0xa2) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)).
  Proof. mk_rvc (PA + 0xa2)%Z (mword_of_int 0xc10d : mword 16)
    (mword_of_int (PA + 0xa2) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 10), BEQ)) padc_c10d exec_execute_C_BEQZ. Qed.

  (* +0xa4  c41ff0ef  jal ra,fileclose *)
  Lemma pai_a4 : kernel_text -∗ instr (mword_of_int (PA + 0xa4) : mword 64) false (JAL (mword_of_int 0x1ffc40 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0xa4)%Z (mword_of_int 0xc41ff0ef : mword 32)
    (mword_of_int (PA + 0xa4) : mword 64) (JAL (mword_of_int 0x1ffc40 : mword 21, Regidx (mword_of_int 1))) padb_c41ff0ef. Qed.

  (* +0xa8  000a3783  ld a5,0(s4) *)
  Lemma pai_a8 : kernel_text -∗ instr (mword_of_int (PA + 0xa8) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_base (PA + 0xa8)%Z (mword_of_int 0x000a3783 : mword 32)
    (mword_of_int (PA + 0xa8) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 8)) padb_000a3783. Qed.

  (* +0xac  557d  c.li a0,-1 *)
  Lemma pai_ac : kernel_text -∗ instr (mword_of_int (PA + 0xac) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (PA + 0xac)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (PA + 0xac) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  (* +0xae  c789  c.beqz a5,+0x0a *)
  Lemma pai_ae : kernel_text -∗ instr (mword_of_int (PA + 0xae) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 15), BEQ)).
  Proof. mk_rvc (PA + 0xae)%Z (mword_of_int 0xc789 : mword 16)
    (mword_of_int (PA + 0xae) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 5 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 15), BEQ)) padc_c789 exec_execute_C_BEQZ. Qed.

  (* +0xb0  853e  c.mv a0,a5 *)
  Lemma pai_b0 : kernel_text -∗ instr (mword_of_int (PA + 0xb0) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PA + 0xb0)%Z (mword_of_int 0x853e : mword 16)
    (mword_of_int (PA + 0xb0) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)) cdec_853e exec_execute_C_MV. Qed.

  (* +0xb2  c33ff0ef  jal ra,fileclose *)
  Lemma pai_b2 : kernel_text -∗ instr (mword_of_int (PA + 0xb2) : mword 64) false (JAL (mword_of_int 0x1ffc32 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PA + 0xb2)%Z (mword_of_int 0xc33ff0ef : mword 32)
    (mword_of_int (PA + 0xb2) : mword 64) (JAL (mword_of_int 0x1ffc32 : mword 21, Regidx (mword_of_int 1))) padb_c33ff0ef. Qed.

  (* +0xb6  557d  c.li a0,-1 *)
  Lemma pai_b6 : kernel_text -∗ instr (mword_of_int (PA + 0xb6) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (PA + 0xb6)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (PA + 0xb6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  (* +0xb8  70a2  c.ldsp ra,40(sp) *)
  Lemma pai_b8 : kernel_text -∗ instr (mword_of_int (PA + 0xb8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PA + 0xb8)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (PA + 0xb8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  (* +0xba  7402  c.ldsp s0,32(sp) *)
  Lemma pai_ba : kernel_text -∗ instr (mword_of_int (PA + 0xba) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PA + 0xba)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (PA + 0xba) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  (* +0xbc  64e2  c.ldsp s1,24(sp) *)
  Lemma pai_bc : kernel_text -∗ instr (mword_of_int (PA + 0xbc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PA + 0xbc)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (PA + 0xbc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  (* +0xbe  6a02  c.ldsp s4,0(sp) *)
  Lemma pai_be : kernel_text -∗ instr (mword_of_int (PA + 0xbe) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PA + 0xbe)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (PA + 0xbe) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  (* +0xc0  6145  c.addi16sp sp,48 *)
  Lemma pai_c0 : kernel_text -∗ instr (mword_of_int (PA + 0xc0) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PA + 0xc0)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (PA + 0xc0) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  (* +0xc2  8082  c.ret *)
  Lemma pai_c2 : kernel_text -∗ instr (mword_of_int (PA + 0xc2) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PA + 0xc2)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PA + 0xc2) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* +0xc4  557d  c.li a0,-1 *)
  Lemma pai_c4 : kernel_text -∗ instr (mword_of_int (PA + 0xc4) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (PA + 0xc4)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (PA + 0xc4) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  (* +0xc6  bfcd  c.j -0x0e *)
  Lemma pai_c6 : kernel_text -∗ instr (mword_of_int (PA + 0xc6) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PA + 0xc6)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (PA + 0xc6) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

End PipeallocInstrs.

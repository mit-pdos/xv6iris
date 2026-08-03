(* CodePipewrite.v -- the instruction-DECODE layer for xv6's pipewrite().
   For EVERY instruction of

     pipewrite @ 0x8000449e .. 0x80004594   (offsets 0x00 .. 0xf6, 95 in all)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pwi_<off>])
   plus the per-instruction decode facts they consume.  Same shape as
   CodePipeclose / CodePipealloc: [mk_rvc] for compressed
   instructions, [mk_base] for 4-byte ones.  Every compressed word the rest
   of the tree already decodes comes from KernelRvcDecode as [cdec_<word>];
   only the words nothing else uses are local ([pwdc_<word>], and
   [pwdb_<word>] for the 4-byte ones).

   pipewrite is SHRINK-WRAPPED: ra/s0..s5 are spilled in the prologue, but
   s6..s10 only on the copy path (+0x28..+0x30), and each of the three arms
   that DID save them reloads exactly those five -- +0x4e (readopen == 0 /
   killed), +0xce (the loop ran out) and +0xec (copyin faulted) -- before
   rejoining the common epilogue at +0x58.  The n <= 0 arm at +0xe8 never
   saved them and so jumps straight to the +0xd8 wakeup/release tail.
   The 1-byte local [ch] lives at s0-97.

   Body (all instruction bytes from the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/pipe.c):

     0x00 7159       addi sp,sp,-112
     0x02 f486       sd ra,104(sp)
     0x04 f0a2       sd s0,96(sp)
     0x06 eca6       sd s1,88(sp)
     0x08 e8ca       sd s2,80(sp)
     0x0a e4ce       sd s3,72(sp)
     0x0c e0d2       sd s4,64(sp)
     0x0e fc56       sd s5,56(sp)
     0x10 1880       addi s0,sp,112
     0x12 84aa       mv s1,a0
     0x14 8aae       mv s5,a1
     0x16 8a32       mv s4,a2
     0x18 c4efd0ef   jal 80001904 <myproc>
     0x1c 89aa       mv s3,a0
     0x1e 8526       mv a0,s1
     0x20 f4afc0ef   jal 80000c08 <acquire>
     0x24 0d405263   blez s4,80004586 <pipewrite+0xe8>
     0x28 f85a       sd s6,48(sp)
     0x2a f45e       sd s7,40(sp)
     0x2c f062       sd s8,32(sp)
     0x2e ec66       sd s9,24(sp)
     0x30 e86a       sd s10,16(sp)
     0x32 4901       li s2,0
     0x34 f9f40c13   addi s8,s0,-97
     0x38 4b85       li s7,1
     0x3a 5b7d       li s6,-1
     0x3c 21848d13   addi s10,s1,536
     0x40 21c48c93   addi s9,s1,540
     0x44 a82d       j 8000451c <pipewrite+0x7e>
     0x46 8526       mv a0,s1
     0x48 faafc0ef   jal 80000c90 <release>
     0x4c 597d       li s2,-1
     0x4e 7b42       ld s6,48(sp)
     0x50 7ba2       ld s7,40(sp)
     0x52 7c02       ld s8,32(sp)
     0x54 6ce2       ld s9,24(sp)
     0x56 6d42       ld s10,16(sp)
     0x58 854a       mv a0,s2
     0x5a 70a6       ld ra,104(sp)
     0x5c 7406       ld s0,96(sp)
     0x5e 64e6       ld s1,88(sp)
     0x60 6946       ld s2,80(sp)
     0x62 69a6       ld s3,72(sp)
     0x64 6a06       ld s4,64(sp)
     0x66 7ae2       ld s5,56(sp)
     0x68 6165       addi sp,sp,112
     0x6a 8082       ret
     0x6c 856a       mv a0,s10
     0x6e a47fd0ef   jal 80001f52 <wakeup>
     0x72 85a6       mv a1,s1
     0x74 8566       mv a0,s9
     0x76 9f3fd0ef   jal 80001f06 <sleep>
     0x7a 05495a63   bge s2,s4,8000456c <pipewrite+0xce>
     0x7e 2204a783   lw a5,544(s1)
     0x82 d3f1       beqz a5,800044e4 <pipewrite+0x46>
     0x84 854e       mv a0,s3
     0x86 c1ffd0ef   jal 80002142 <killed>
     0x8a fd55       bnez a0,800044e4 <pipewrite+0x46>
     0x8c 2184a783   lw a5,536(s1)
     0x90 21c4a703   lw a4,540(s1)
     0x94 2007879b   addiw a5,a5,512
     0x98 fcf70ae3   beq a4,a5,8000450a <pipewrite+0x6c>
     0x9c 86de       mv a3,s7
     0x9e 01590633   add a2,s2,s5
     0xa2 85e2       mv a1,s8
     0xa4 0509b503   ld a0,80(s3)
     0xa8 99cfd0ef   jal 800016e2 <copyin>
     0xac 05650063   beq a0,s6,8000458a <pipewrite+0xec>
     0xb0 21c4a783   lw a5,540(s1)
     0xb4 0017871b   addiw a4,a5,1
     0xb8 20e4ae23   sw a4,540(s1)
     0xbc 1ff7f793   andi a5,a5,511
     0xc0 97a6       add a5,a5,s1
     0xc2 f9f44703   lbu a4,-97(s0)
     0xc6 00e78c23   sb a4,24(a5)
     0xca 2905       addiw s2,s2,1
     0xcc b77d       j 80004518 <pipewrite+0x7a>
     0xce 7b42       ld s6,48(sp)
     0xd0 7ba2       ld s7,40(sp)
     0xd2 7c02       ld s8,32(sp)
     0xd4 6ce2       ld s9,24(sp)
     0xd6 6d42       ld s10,16(sp)
     0xd8 21848513   addi a0,s1,536
     0xdc 9d9fd0ef   jal 80001f52 <wakeup>
     0xe0 8526       mv a0,s1
     0xe2 f10fc0ef   jal 80000c90 <release>
     0xe6 bf8d       j 800044f6 <pipewrite+0x58>
     0xe8 4901       li s2,0
     0xea b7fd       j 80004576 <pipewrite+0xd8>
     0xec 7b42       ld s6,48(sp)
     0xee 7ba2       ld s7,40(sp)
     0xf0 7c02       ld s8,32(sp)
     0xf2 6ce2       ld s9,24(sp)
     0xf4 6d42       ld s10,16(sp)
     0xf6 b7cd       j 80004576 <pipewrite+0xd8>
                                                                          *)
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

Notation PW := KernelSyms.pipewrite.

(* ===================================================================== *)
(* Compressed decode facts for the words no other function uses.          *)
(* ===================================================================== *)

(* 0x7159  addi sp,sp,-112 *)
Lemma pwdc_7159 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7159 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 57 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf486  sd ra,104(sp) *)
Lemma pwdc_f486 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf486 : mword 16)) s
  = Some (C_SDSP (mword_of_int 13, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf0a2  sd s0,96(sp) *)
Lemma pwdc_f0a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0a2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 12, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xeca6  sd s1,88(sp) *)
Lemma pwdc_eca6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeca6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 11, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe8ca  sd s2,80(sp) *)
Lemma pwdc_e8ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8ca : mword 16)) s
  = Some (C_SDSP (mword_of_int 10, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe4ce  sd s3,72(sp) *)
Lemma pwdc_e4ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe4ce : mword 16)) s
  = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe0d2  sd s4,64(sp) *)
Lemma pwdc_e0d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe0d2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 8, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfc56  sd s5,56(sp) *)
Lemma pwdc_fc56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc56 : mword 16)) s
  = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1880  addi s0,sp,112 *)
Lemma pwdc_1880 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1880 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 28 : mword 8), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x8a32  mv s4,a2 *)
(* [cdec_8a32] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0xf85a  sd s6,48(sp) *)
Lemma pwdc_f85a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf85a : mword 16)) s
  = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf45e  sd s7,40(sp) *)
Lemma pwdc_f45e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf45e : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf062  sd s8,32(sp) *)
Lemma pwdc_f062 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf062 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec66  sd s9,24(sp) *)
Lemma pwdc_ec66 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec66 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe86a  sd s10,16(sp) *)
Lemma pwdc_e86a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe86a : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* [cdec_4b85] (li s7,1) -- shared, see KernelRvcDecode.v *)



(* 0x597d  li s2,-1 *)
Lemma pwdc_597d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x597d : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7b42  ld s6,48(sp) *)
Lemma pwdc_7b42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7b42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7ba2  ld s7,40(sp) *)
Lemma pwdc_7ba2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ba2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7c02  ld s8,32(sp) *)
Lemma pwdc_7c02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7c02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6ce2  ld s9,24(sp) *)
Lemma pwdc_6ce2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6ce2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6d42  ld s10,16(sp) *)
Lemma pwdc_6d42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6d42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70a6  ld ra,104(sp) *)
Lemma pwdc_70a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70a6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7406  ld s0,96(sp) *)
Lemma pwdc_7406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7406 : mword 16)) s
  = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64e6  ld s1,88(sp) *)
Lemma pwdc_64e6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64e6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6946  ld s2,80(sp) *)
Lemma pwdc_6946 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6946 : mword 16)) s
  = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x69a6  ld s3,72(sp) *)
Lemma pwdc_69a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69a6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6a06  ld s4,64(sp) *)
Lemma pwdc_6a06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a06 : mword 16)) s
  = Some (C_LDSP (mword_of_int 8, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7ae2  ld s5,56(sp) *)
Lemma pwdc_7ae2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ae2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6165  addi sp,sp,112 *)
Lemma pwdc_6165 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6165 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 7 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x856a  mv a0,s10 *)
Lemma pwdc_856a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x856a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8566  mv a0,s9 *)
Lemma pwdc_8566 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8566 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd3f1  beqz a5,800044e4 <pipewrite+0x46> *)
Lemma pwdc_d3f1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd3f1 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 226, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0xfd55  bnez a0,800044e4 <pipewrite+0x46> *)
Lemma pwdc_fd55 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfd55 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 222, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x85e2  mv a1,s8 *)
Lemma pwdc_85e2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85e2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.




(* 0xbf8d  j 800044f6 <pipewrite+0x58> *)
Lemma pwdc_bf8d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf8d : mword 16)) s
  = Some (C_J (mword_of_int 1977), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_b7cd] -- shared, see KernelRvcDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0xc4efd0ef  jal 80001904 <myproc> *)
Lemma pwdb_c4efd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc4efd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2085966 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xf4afc0ef  jal 80000c08 <acquire> *)
Lemma pwdb_f4afc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf4afc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082634 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0d405263  blez s4,80004586 <pipewrite+0xe8> *)
Lemma pwdb_0d405263 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0d405263 : mword 32)) s
  = Some (BTYPE (mword_of_int 196 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0xf9f40c13  addi s8,s0,-97 *)
Lemma pwdb_f9f40c13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9f40c13 : mword 32)) s
  = Some (ITYPE (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x21848d13  addi s10,s1,536 *)
Lemma pwdb_21848d13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21848d13 : mword 32)) s
  = Some (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 26), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x21c48c93  addi s9,s1,540 *)
Lemma pwdb_21c48c93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21c48c93 : mword 32)) s
  = Some (ITYPE (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 25), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfaafc0ef  jal 80000c90 <release> *)
Lemma pwdb_faafc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaafc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082730 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xa47fd0ef  jal 80001f52 <wakeup> *)
Lemma pwdb_a47fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa47fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087494 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x9f3fd0ef  jal 80001f06 <sleep> *)
Lemma pwdb_9f3fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9f3fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087410 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x05495a63  bge s2,s4,8000456c <pipewrite+0xce> *)
Lemma pwdb_05495a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05495a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BGE), s).
Proof. decode_bridge_ms. Qed.


(* 0xc1ffd0ef  jal 80002142 <killed> *)
Lemma pwdb_c1ffd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc1ffd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087966 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.



(* 0x2007879b  addiw a5,a5,512 *)
Lemma pwdb_2007879b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2007879b : mword 32)) s
  = Some (ADDIW (mword_of_int 512 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfcf70ae3  beq a4,a5,8000450a <pipewrite+0x6c> *)
Lemma pwdb_fcf70ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfcf70ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8148 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x01590633  add a2,s2,s5 *)
Lemma pwdb_01590633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01590633 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 18), Regidx (mword_of_int 12), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x0509b503  ld a0,80(s3) *)
Lemma pwdb_0509b503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0509b503 : mword 32)) s
  = Some (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x99cfd0ef  jal 800016e2 <copyin> *)
Lemma pwdb_99cfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x99cfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2085276 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x05650063  beq a0,s6,8000458a <pipewrite+0xec> *)
Lemma pwdb_05650063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05650063 : mword 32)) s
  = Some (BTYPE (mword_of_int 64 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.


(* 0x0017871b  addiw a4,a5,1 *)
Lemma pwdb_0017871b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017871b : mword 32)) s
  = Some (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14)), s).
Proof. decode_bridge_ms. Qed.

(* 0x20e4ae23  sw a4,540(s1) *)
Lemma pwdb_20e4ae23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x20e4ae23 : mword 32)) s
  = Some (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.


(* 0xf9f44703  lbu a4,-97(s0) *)
Lemma pwdb_f9f44703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf9f44703 : mword 32)) s
  = Some (LOAD (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), true, 1), s).
Proof. decode_bridge_ms. Qed.



(* 0x9d9fd0ef  jal 80001f52 <wakeup> *)
Lemma pwdb_9d9fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9d9fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087384 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xf10fc0ef  jal 80000c90 <release> *)
Lemma pwdb_f10fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf10fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082576 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section PipewriteInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* +0x00  7159  addi sp,sp,-112 *)
  Lemma pwi_00 : kernel_text -∗ instr (mword_of_int (PW + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 57 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PW + 0x00)%Z (mword_of_int 0x7159 : mword 16)
    (mword_of_int (PW + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 57 : mword 6), sp, sp, ADDI)) pwdc_7159 exec_execute_C_ADDI16SP. Qed.

  (* +0x02  f486  sd ra,104(sp) *)
  Lemma pwi_02 : kernel_text -∗ instr (mword_of_int (PW + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PW + 0x02)%Z (mword_of_int 0xf486 : mword 16)
    (mword_of_int (PW + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) pwdc_f486 exec_execute_C_SDSP. Qed.

  (* +0x04  f0a2  sd s0,96(sp) *)
  Lemma pwi_04 : kernel_text -∗ instr (mword_of_int (PW + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PW + 0x04)%Z (mword_of_int 0xf0a2 : mword 16)
    (mword_of_int (PW + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) pwdc_f0a2 exec_execute_C_SDSP. Qed.

  (* +0x06  eca6  sd s1,88(sp) *)
  Lemma pwi_06 : kernel_text -∗ instr (mword_of_int (PW + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PW + 0x06)%Z (mword_of_int 0xeca6 : mword 16)
    (mword_of_int (PW + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) pwdc_eca6 exec_execute_C_SDSP. Qed.

  (* +0x08  e8ca  sd s2,80(sp) *)
  Lemma pwi_08 : kernel_text -∗ instr (mword_of_int (PW + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PW + 0x08)%Z (mword_of_int 0xe8ca : mword 16)
    (mword_of_int (PW + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) pwdc_e8ca exec_execute_C_SDSP. Qed.

  (* +0x0a  e4ce  sd s3,72(sp) *)
  Lemma pwi_0a : kernel_text -∗ instr (mword_of_int (PW + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (PW + 0x0a)%Z (mword_of_int 0xe4ce : mword 16)
    (mword_of_int (PW + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) pwdc_e4ce exec_execute_C_SDSP. Qed.

  (* +0x0c  e0d2  sd s4,64(sp) *)
  Lemma pwi_0c : kernel_text -∗ instr (mword_of_int (PW + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (PW + 0x0c)%Z (mword_of_int 0xe0d2 : mword 16)
    (mword_of_int (PW + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) pwdc_e0d2 exec_execute_C_SDSP. Qed.

  (* +0x0e  fc56  sd s5,56(sp) *)
  Lemma pwi_0e : kernel_text -∗ instr (mword_of_int (PW + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (PW + 0x0e)%Z (mword_of_int 0xfc56 : mword 16)
    (mword_of_int (PW + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) pwdc_fc56 exec_execute_C_SDSP. Qed.

  (* +0x10  1880  addi s0,sp,112 *)
  Lemma pwi_10 : kernel_text -∗ instr (mword_of_int (PW + 0x10) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 28 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PW + 0x10)%Z (mword_of_int 0x1880 : mword 16)
    (mword_of_int (PW + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 28 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) pwdc_1880 exec_execute_C_ADDI4SPN. Qed.

  (* +0x12  84aa  mv s1,a0 *)
  Lemma pwi_12 : kernel_text -∗ instr (mword_of_int (PW + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PW + 0x12)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (PW + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* +0x14  8aae  mv s5,a1 *)
  Lemma pwi_14 : kernel_text -∗ instr (mword_of_int (PW + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (PW + 0x14)%Z (mword_of_int 0x8aae : mword 16)
    (mword_of_int (PW + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 21), ADD)) cdec_8aae exec_execute_C_MV. Qed.

  (* +0x16  8a32  mv s4,a2 *)
  Lemma pwi_16 : kernel_text -∗ instr (mword_of_int (PW + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (PW + 0x16)%Z (mword_of_int 0x8a32 : mword 16)
    (mword_of_int (PW + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a32 exec_execute_C_MV. Qed.

  (* +0x18  c4efd0ef  jal 80001904 <myproc> *)
  Lemma pwi_18 : kernel_text -∗ instr (mword_of_int (PW + 0x18) : mword 64) false (JAL (mword_of_int 2085966 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x18)%Z (mword_of_int 0xc4efd0ef : mword 32)
    (mword_of_int (PW + 0x18) : mword 64) (JAL (mword_of_int 2085966 : mword 21, Regidx (mword_of_int 1))) pwdb_c4efd0ef. Qed.

  (* +0x1c  89aa  mv s3,a0 *)
  Lemma pwi_1c : kernel_text -∗ instr (mword_of_int (PW + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (PW + 0x1c)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (PW + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  (* +0x1e  8526  mv a0,s1 *)
  Lemma pwi_1e : kernel_text -∗ instr (mword_of_int (PW + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x1e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PW + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0x20  f4afc0ef  jal 80000c08 <acquire> *)
  Lemma pwi_20 : kernel_text -∗ instr (mword_of_int (PW + 0x20) : mword 64) false (JAL (mword_of_int 2082634 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x20)%Z (mword_of_int 0xf4afc0ef : mword 32)
    (mword_of_int (PW + 0x20) : mword 64) (JAL (mword_of_int 2082634 : mword 21, Regidx (mword_of_int 1))) pwdb_f4afc0ef. Qed.

  (* +0x24  0d405263  blez s4,80004586 <pipewrite+0xe8> *)
  Lemma pwi_24 : kernel_text -∗ instr (mword_of_int (PW + 0x24) : mword 64) false (BTYPE (mword_of_int 196 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PW + 0x24)%Z (mword_of_int 0x0d405263 : mword 32)
    (mword_of_int (PW + 0x24) : mword 64) (BTYPE (mword_of_int 196 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 0), BGE)) pwdb_0d405263. Qed.

  (* +0x28  f85a  sd s6,48(sp) *)
  Lemma pwi_28 : kernel_text -∗ instr (mword_of_int (PW + 0x28) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PW + 0x28)%Z (mword_of_int 0xf85a : mword 16)
    (mword_of_int (PW + 0x28) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) pwdc_f85a exec_execute_C_SDSP. Qed.

  (* +0x2a  f45e  sd s7,40(sp) *)
  Lemma pwi_2a : kernel_text -∗ instr (mword_of_int (PW + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (PW + 0x2a)%Z (mword_of_int 0xf45e : mword 16)
    (mword_of_int (PW + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) pwdc_f45e exec_execute_C_SDSP. Qed.

  (* +0x2c  f062  sd s8,32(sp) *)
  Lemma pwi_2c : kernel_text -∗ instr (mword_of_int (PW + 0x2c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (PW + 0x2c)%Z (mword_of_int 0xf062 : mword 16)
    (mword_of_int (PW + 0x2c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) pwdc_f062 exec_execute_C_SDSP. Qed.

  (* +0x2e  ec66  sd s9,24(sp) *)
  Lemma pwi_2e : kernel_text -∗ instr (mword_of_int (PW + 0x2e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)).
  Proof. mk_rvc (PW + 0x2e)%Z (mword_of_int 0xec66 : mword 16)
    (mword_of_int (PW + 0x2e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)) pwdc_ec66 exec_execute_C_SDSP. Qed.

  (* +0x30  e86a  sd s10,16(sp) *)
  Lemma pwi_30 : kernel_text -∗ instr (mword_of_int (PW + 0x30) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)).
  Proof. mk_rvc (PW + 0x30)%Z (mword_of_int 0xe86a : mword 16)
    (mword_of_int (PW + 0x30) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)) pwdc_e86a exec_execute_C_SDSP. Qed.

  (* +0x32  4901  li s2,0 *)
  Lemma pwi_32 : kernel_text -∗ instr (mword_of_int (PW + 0x32) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (PW + 0x32)%Z (mword_of_int 0x4901 : mword 16)
    (mword_of_int (PW + 0x32) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)) cdec_4901 exec_execute_C_LI. Qed.

  (* +0x34  f9f40c13  addi s8,s0,-97 *)
  Lemma pwi_34 : kernel_text -∗ instr (mword_of_int (PW + 0x34) : mword 64) false (ITYPE (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI)).
  Proof. mk_base (PW + 0x34)%Z (mword_of_int 0xf9f40c13 : mword 32)
    (mword_of_int (PW + 0x34) : mword 64) (ITYPE (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI)) pwdb_f9f40c13. Qed.

  (* +0x38  4b85  li s7,1 *)
  Lemma pwi_38 : kernel_text -∗ instr (mword_of_int (PW + 0x38) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)).
  Proof. mk_rvc (PW + 0x38)%Z (mword_of_int 0x4b85 : mword 16)
    (mword_of_int (PW + 0x38) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)) cdec_4b85 exec_execute_C_LI. Qed.

  (* +0x3a  5b7d  li s6,-1 *)
  Lemma pwi_3a : kernel_text -∗ instr (mword_of_int (PW + 0x3a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)).
  Proof. mk_rvc (PW + 0x3a)%Z (mword_of_int 0x5b7d : mword 16)
    (mword_of_int (PW + 0x3a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)) cdec_5b7d exec_execute_C_LI. Qed.

  (* +0x3c  21848d13  addi s10,s1,536 *)
  Lemma pwi_3c : kernel_text -∗ instr (mword_of_int (PW + 0x3c) : mword 64) false (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 26), ADDI)).
  Proof. mk_base (PW + 0x3c)%Z (mword_of_int 0x21848d13 : mword 32)
    (mword_of_int (PW + 0x3c) : mword 64) (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 26), ADDI)) pwdb_21848d13. Qed.

  (* +0x40  21c48c93  addi s9,s1,540 *)
  Lemma pwi_40 : kernel_text -∗ instr (mword_of_int (PW + 0x40) : mword 64) false (ITYPE (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 25), ADDI)).
  Proof. mk_base (PW + 0x40)%Z (mword_of_int 0x21c48c93 : mword 32)
    (mword_of_int (PW + 0x40) : mword 64) (ITYPE (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 25), ADDI)) pwdb_21c48c93. Qed.

  (* +0x44  a82d  j 8000451c <pipewrite+0x7e> *)
  Lemma pwi_44 : kernel_text -∗ instr (mword_of_int (PW + 0x44) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PW + 0x44)%Z (mword_of_int 0xa82d : mword 16)
    (mword_of_int (PW + 0x44) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")), zreg)) cdec_a82d exec_execute_C_J. Qed.

  (* +0x46  8526  mv a0,s1 *)
  Lemma pwi_46 : kernel_text -∗ instr (mword_of_int (PW + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x46)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PW + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0x48  faafc0ef  jal 80000c90 <release> *)
  Lemma pwi_48 : kernel_text -∗ instr (mword_of_int (PW + 0x48) : mword 64) false (JAL (mword_of_int 2082730 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x48)%Z (mword_of_int 0xfaafc0ef : mword 32)
    (mword_of_int (PW + 0x48) : mword 64) (JAL (mword_of_int 2082730 : mword 21, Regidx (mword_of_int 1))) pwdb_faafc0ef. Qed.

  (* +0x4c  597d  li s2,-1 *)
  Lemma pwi_4c : kernel_text -∗ instr (mword_of_int (PW + 0x4c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (PW + 0x4c)%Z (mword_of_int 0x597d : mword 16)
    (mword_of_int (PW + 0x4c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)) pwdc_597d exec_execute_C_LI. Qed.

  (* +0x4e  7b42  ld s6,48(sp) *)
  Lemma pwi_4e : kernel_text -∗ instr (mword_of_int (PW + 0x4e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PW + 0x4e)%Z (mword_of_int 0x7b42 : mword 16)
    (mword_of_int (PW + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) pwdc_7b42 exec_execute_C_LDSP. Qed.

  (* +0x50  7ba2  ld s7,40(sp) *)
  Lemma pwi_50 : kernel_text -∗ instr (mword_of_int (PW + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PW + 0x50)%Z (mword_of_int 0x7ba2 : mword 16)
    (mword_of_int (PW + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) pwdc_7ba2 exec_execute_C_LDSP. Qed.

  (* +0x52  7c02  ld s8,32(sp) *)
  Lemma pwi_52 : kernel_text -∗ instr (mword_of_int (PW + 0x52) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PW + 0x52)%Z (mword_of_int 0x7c02 : mword 16)
    (mword_of_int (PW + 0x52) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) pwdc_7c02 exec_execute_C_LDSP. Qed.

  (* +0x54  6ce2  ld s9,24(sp) *)
  Lemma pwi_54 : kernel_text -∗ instr (mword_of_int (PW + 0x54) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (PW + 0x54)%Z (mword_of_int 0x6ce2 : mword 16)
    (mword_of_int (PW + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) pwdc_6ce2 exec_execute_C_LDSP. Qed.

  (* +0x56  6d42  ld s10,16(sp) *)
  Lemma pwi_56 : kernel_text -∗ instr (mword_of_int (PW + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (PW + 0x56)%Z (mword_of_int 0x6d42 : mword 16)
    (mword_of_int (PW + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) pwdc_6d42 exec_execute_C_LDSP. Qed.

  (* +0x58  854a  mv a0,s2 *)
  Lemma pwi_58 : kernel_text -∗ instr (mword_of_int (PW + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x58)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (PW + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* +0x5a  70a6  ld ra,104(sp) *)
  Lemma pwi_5a : kernel_text -∗ instr (mword_of_int (PW + 0x5a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PW + 0x5a)%Z (mword_of_int 0x70a6 : mword 16)
    (mword_of_int (PW + 0x5a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) pwdc_70a6 exec_execute_C_LDSP. Qed.

  (* +0x5c  7406  ld s0,96(sp) *)
  Lemma pwi_5c : kernel_text -∗ instr (mword_of_int (PW + 0x5c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PW + 0x5c)%Z (mword_of_int 0x7406 : mword 16)
    (mword_of_int (PW + 0x5c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) pwdc_7406 exec_execute_C_LDSP. Qed.

  (* +0x5e  64e6  ld s1,88(sp) *)
  Lemma pwi_5e : kernel_text -∗ instr (mword_of_int (PW + 0x5e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PW + 0x5e)%Z (mword_of_int 0x64e6 : mword 16)
    (mword_of_int (PW + 0x5e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) pwdc_64e6 exec_execute_C_LDSP. Qed.

  (* +0x60  6946  ld s2,80(sp) *)
  Lemma pwi_60 : kernel_text -∗ instr (mword_of_int (PW + 0x60) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PW + 0x60)%Z (mword_of_int 0x6946 : mword 16)
    (mword_of_int (PW + 0x60) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) pwdc_6946 exec_execute_C_LDSP. Qed.

  (* +0x62  69a6  ld s3,72(sp) *)
  Lemma pwi_62 : kernel_text -∗ instr (mword_of_int (PW + 0x62) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PW + 0x62)%Z (mword_of_int 0x69a6 : mword 16)
    (mword_of_int (PW + 0x62) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) pwdc_69a6 exec_execute_C_LDSP. Qed.

  (* +0x64  6a06  ld s4,64(sp) *)
  Lemma pwi_64 : kernel_text -∗ instr (mword_of_int (PW + 0x64) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PW + 0x64)%Z (mword_of_int 0x6a06 : mword 16)
    (mword_of_int (PW + 0x64) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) pwdc_6a06 exec_execute_C_LDSP. Qed.

  (* +0x66  7ae2  ld s5,56(sp) *)
  Lemma pwi_66 : kernel_text -∗ instr (mword_of_int (PW + 0x66) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (PW + 0x66)%Z (mword_of_int 0x7ae2 : mword 16)
    (mword_of_int (PW + 0x66) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) pwdc_7ae2 exec_execute_C_LDSP. Qed.

  (* +0x68  6165  addi sp,sp,112 *)
  Lemma pwi_68 : kernel_text -∗ instr (mword_of_int (PW + 0x68) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 7 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PW + 0x68)%Z (mword_of_int 0x6165 : mword 16)
    (mword_of_int (PW + 0x68) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 7 : mword 6), sp, sp, ADDI)) pwdc_6165 exec_execute_C_ADDI16SP. Qed.

  (* +0x6a  8082  ret *)
  Lemma pwi_6a : kernel_text -∗ instr (mword_of_int (PW + 0x6a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PW + 0x6a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PW + 0x6a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* +0x6c  856a  mv a0,s10 *)
  Lemma pwi_6c : kernel_text -∗ instr (mword_of_int (PW + 0x6c) : mword 64) true (RTYPE (Regidx (mword_of_int 26), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x6c)%Z (mword_of_int 0x856a : mword 16)
    (mword_of_int (PW + 0x6c) : mword 64) (RTYPE (Regidx (mword_of_int 26), zreg, Regidx (mword_of_int 10), ADD)) pwdc_856a exec_execute_C_MV. Qed.

  (* +0x6e  a47fd0ef  jal 80001f52 <wakeup> *)
  Lemma pwi_6e : kernel_text -∗ instr (mword_of_int (PW + 0x6e) : mword 64) false (JAL (mword_of_int 2087494 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x6e)%Z (mword_of_int 0xa47fd0ef : mword 32)
    (mword_of_int (PW + 0x6e) : mword 64) (JAL (mword_of_int 2087494 : mword 21, Regidx (mword_of_int 1))) pwdb_a47fd0ef. Qed.

  (* +0x72  85a6  mv a1,s1 *)
  Lemma pwi_72 : kernel_text -∗ instr (mword_of_int (PW + 0x72) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PW + 0x72)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (PW + 0x72) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* +0x74  8566  mv a0,s9 *)
  Lemma pwi_74 : kernel_text -∗ instr (mword_of_int (PW + 0x74) : mword 64) true (RTYPE (Regidx (mword_of_int 25), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x74)%Z (mword_of_int 0x8566 : mword 16)
    (mword_of_int (PW + 0x74) : mword 64) (RTYPE (Regidx (mword_of_int 25), zreg, Regidx (mword_of_int 10), ADD)) pwdc_8566 exec_execute_C_MV. Qed.

  (* +0x76  9f3fd0ef  jal 80001f06 <sleep> *)
  Lemma pwi_76 : kernel_text -∗ instr (mword_of_int (PW + 0x76) : mword 64) false (JAL (mword_of_int 2087410 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x76)%Z (mword_of_int 0x9f3fd0ef : mword 32)
    (mword_of_int (PW + 0x76) : mword 64) (JAL (mword_of_int 2087410 : mword 21, Regidx (mword_of_int 1))) pwdb_9f3fd0ef. Qed.

  (* +0x7a  05495a63  bge s2,s4,8000456c <pipewrite+0xce> *)
  Lemma pwi_7a : kernel_text -∗ instr (mword_of_int (PW + 0x7a) : mword 64) false (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BGE)).
  Proof. mk_base (PW + 0x7a)%Z (mword_of_int 0x05495a63 : mword 32)
    (mword_of_int (PW + 0x7a) : mword 64) (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BGE)) pwdb_05495a63. Qed.

  (* +0x7e  2204a783  lw a5,544(s1) *)
  Lemma pwi_7e : kernel_text -∗ instr (mword_of_int (PW + 0x7e) : mword 64) false (LOAD (mword_of_int 544 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PW + 0x7e)%Z (mword_of_int 0x2204a783 : mword 32)
    (mword_of_int (PW + 0x7e) : mword 64) (LOAD (mword_of_int 544 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2204a783. Qed.

  (* +0x82  d3f1  beqz a5,800044e4 <pipewrite+0x46> *)
  Lemma pwi_82 : kernel_text -∗ instr (mword_of_int (PW + 0x82) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 226 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PW + 0x82)%Z (mword_of_int 0xd3f1 : mword 16)
    (mword_of_int (PW + 0x82) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 226 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) pwdc_d3f1 exec_execute_C_BEQZ. Qed.

  (* +0x84  854e  mv a0,s3 *)
  Lemma pwi_84 : kernel_text -∗ instr (mword_of_int (PW + 0x84) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0x84)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (PW + 0x84) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  (* +0x86  c1ffd0ef  jal 80002142 <killed> *)
  Lemma pwi_86 : kernel_text -∗ instr (mword_of_int (PW + 0x86) : mword 64) false (JAL (mword_of_int 2087966 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0x86)%Z (mword_of_int 0xc1ffd0ef : mword 32)
    (mword_of_int (PW + 0x86) : mword 64) (JAL (mword_of_int 2087966 : mword 21, Regidx (mword_of_int 1))) pwdb_c1ffd0ef. Qed.

  (* +0x8a  fd55  bnez a0,800044e4 <pipewrite+0x46> *)
  Lemma pwi_8a : kernel_text -∗ instr (mword_of_int (PW + 0x8a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 222 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (PW + 0x8a)%Z (mword_of_int 0xfd55 : mword 16)
    (mword_of_int (PW + 0x8a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 222 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) pwdc_fd55 exec_execute_C_BNEZ. Qed.

  (* +0x8c  2184a783  lw a5,536(s1) *)
  Lemma pwi_8c : kernel_text -∗ instr (mword_of_int (PW + 0x8c) : mword 64) false (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PW + 0x8c)%Z (mword_of_int 0x2184a783 : mword 32)
    (mword_of_int (PW + 0x8c) : mword 64) (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2184a783. Qed.

  (* +0x90  21c4a703  lw a4,540(s1) *)
  Lemma pwi_90 : kernel_text -∗ instr (mword_of_int (PW + 0x90) : mword 64) false (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (PW + 0x90)%Z (mword_of_int 0x21c4a703 : mword 32)
    (mword_of_int (PW + 0x90) : mword 64) (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) bdec_21c4a703. Qed.

  (* +0x94  2007879b  addiw a5,a5,512 *)
  Lemma pwi_94 : kernel_text -∗ instr (mword_of_int (PW + 0x94) : mword 64) false (ADDIW (mword_of_int 512 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_base (PW + 0x94)%Z (mword_of_int 0x2007879b : mword 32)
    (mword_of_int (PW + 0x94) : mword 64) (ADDIW (mword_of_int 512 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15))) pwdb_2007879b. Qed.

  (* +0x98  fcf70ae3  beq a4,a5,8000450a <pipewrite+0x6c> *)
  Lemma pwi_98 : kernel_text -∗ instr (mword_of_int (PW + 0x98) : mword 64) false (BTYPE (mword_of_int 8148 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (PW + 0x98)%Z (mword_of_int 0xfcf70ae3 : mword 32)
    (mword_of_int (PW + 0x98) : mword 64) (BTYPE (mword_of_int 8148 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) pwdb_fcf70ae3. Qed.

  (* +0x9c  86de  mv a3,s7 *)
  Lemma pwi_9c : kernel_text -∗ instr (mword_of_int (PW + 0x9c) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (PW + 0x9c)%Z (mword_of_int 0x86de : mword 16)
    (mword_of_int (PW + 0x9c) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 13), ADD)) cdec_86de exec_execute_C_MV. Qed.

  (* +0x9e  01590633  add a2,s2,s5 *)
  Lemma pwi_9e : kernel_text -∗ instr (mword_of_int (PW + 0x9e) : mword 64) false (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 18), Regidx (mword_of_int 12), ADD)).
  Proof. mk_base (PW + 0x9e)%Z (mword_of_int 0x01590633 : mword 32)
    (mword_of_int (PW + 0x9e) : mword 64) (RTYPE (Regidx (mword_of_int 21), Regidx (mword_of_int 18), Regidx (mword_of_int 12), ADD)) pwdb_01590633. Qed.

  (* +0xa2  85e2  mv a1,s8 *)
  Lemma pwi_a2 : kernel_text -∗ instr (mword_of_int (PW + 0xa2) : mword 64) true (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PW + 0xa2)%Z (mword_of_int 0x85e2 : mword 16)
    (mword_of_int (PW + 0xa2) : mword 64) (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 11), ADD)) pwdc_85e2 exec_execute_C_MV. Qed.

  (* +0xa4  0509b503  ld a0,80(s3) *)
  Lemma pwi_a4 : kernel_text -∗ instr (mword_of_int (PW + 0xa4) : mword 64) false (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (PW + 0xa4)%Z (mword_of_int 0x0509b503 : mword 32)
    (mword_of_int (PW + 0xa4) : mword 64) (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 10), false, 8)) pwdb_0509b503. Qed.

  (* +0xa8  99cfd0ef  jal 800016e2 <copyin> *)
  Lemma pwi_a8 : kernel_text -∗ instr (mword_of_int (PW + 0xa8) : mword 64) false (JAL (mword_of_int 2085276 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0xa8)%Z (mword_of_int 0x99cfd0ef : mword 32)
    (mword_of_int (PW + 0xa8) : mword 64) (JAL (mword_of_int 2085276 : mword 21, Regidx (mword_of_int 1))) pwdb_99cfd0ef. Qed.

  (* +0xac  05650063  beq a0,s6,8000458a <pipewrite+0xec> *)
  Lemma pwi_ac : kernel_text -∗ instr (mword_of_int (PW + 0xac) : mword 64) false (BTYPE (mword_of_int 64 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (PW + 0xac)%Z (mword_of_int 0x05650063 : mword 32)
    (mword_of_int (PW + 0xac) : mword 64) (BTYPE (mword_of_int 64 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ)) pwdb_05650063. Qed.

  (* +0xb0  21c4a783  lw a5,540(s1) *)
  Lemma pwi_b0 : kernel_text -∗ instr (mword_of_int (PW + 0xb0) : mword 64) false (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PW + 0xb0)%Z (mword_of_int 0x21c4a783 : mword 32)
    (mword_of_int (PW + 0xb0) : mword 64) (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_21c4a783. Qed.

  (* +0xb4  0017871b  addiw a4,a5,1 *)
  Lemma pwi_b4 : kernel_text -∗ instr (mword_of_int (PW + 0xb4) : mword 64) false (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14))).
  Proof. mk_base (PW + 0xb4)%Z (mword_of_int 0x0017871b : mword 32)
    (mword_of_int (PW + 0xb4) : mword 64) (ADDIW (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14))) pwdb_0017871b. Qed.

  (* +0xb8  20e4ae23  sw a4,540(s1) *)
  Lemma pwi_b8 : kernel_text -∗ instr (mword_of_int (PW + 0xb8) : mword 64) false (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (PW + 0xb8)%Z (mword_of_int 0x20e4ae23 : mword 32)
    (mword_of_int (PW + 0xb8) : mword 64) (STORE (mword_of_int 540 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 9), 4)) pwdb_20e4ae23. Qed.

  (* +0xbc  1ff7f793  andi a5,a5,511 *)
  Lemma pwi_bc : kernel_text -∗ instr (mword_of_int (PW + 0xbc) : mword 64) false (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (PW + 0xbc)%Z (mword_of_int 0x1ff7f793 : mword 32)
    (mword_of_int (PW + 0xbc) : mword 64) (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) bdec_1ff7f793. Qed.

  (* +0xc0  97a6  add a5,a5,s1 *)
  Lemma pwi_c0 : kernel_text -∗ instr (mword_of_int (PW + 0xc0) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PW + 0xc0)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (PW + 0xc0) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  (* +0xc2  f9f44703  lbu a4,-97(s0) *)
  Lemma pwi_c2 : kernel_text -∗ instr (mword_of_int (PW + 0xc2) : mword 64) false (LOAD (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), true, 1)).
  Proof. mk_base (PW + 0xc2)%Z (mword_of_int 0xf9f44703 : mword 32)
    (mword_of_int (PW + 0xc2) : mword 64) (LOAD (mword_of_int 3999 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), true, 1)) pwdb_f9f44703. Qed.

  (* +0xc6  00e78c23  sb a4,24(a5) *)
  Lemma pwi_c6 : kernel_text -∗ instr (mword_of_int (PW + 0xc6) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)).
  Proof. mk_base (PW + 0xc6)%Z (mword_of_int 0x00e78c23 : mword 32)
    (mword_of_int (PW + 0xc6) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)) bdec_00e78c23. Qed.

  (* +0xca  2905  addiw s2,s2,1 *)
  Lemma pwi_ca : kernel_text -∗ instr (mword_of_int (PW + 0xca) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))).
  Proof. mk_rvc (PW + 0xca)%Z (mword_of_int 0x2905 : mword 16)
    (mword_of_int (PW + 0xca) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))) cdec_2905 exec_execute_C_ADDIW. Qed.

  (* +0xcc  b77d  j 80004518 <pipewrite+0x7a> *)
  Lemma pwi_cc : kernel_text -∗ instr (mword_of_int (PW + 0xcc) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PW + 0xcc)%Z (mword_of_int 0xb77d : mword 16)
    (mword_of_int (PW + 0xcc) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)) cdec_b77d exec_execute_C_J. Qed.

  (* +0xce  7b42  ld s6,48(sp) *)
  Lemma pwi_ce : kernel_text -∗ instr (mword_of_int (PW + 0xce) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PW + 0xce)%Z (mword_of_int 0x7b42 : mword 16)
    (mword_of_int (PW + 0xce) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) pwdc_7b42 exec_execute_C_LDSP. Qed.

  (* +0xd0  7ba2  ld s7,40(sp) *)
  Lemma pwi_d0 : kernel_text -∗ instr (mword_of_int (PW + 0xd0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PW + 0xd0)%Z (mword_of_int 0x7ba2 : mword 16)
    (mword_of_int (PW + 0xd0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) pwdc_7ba2 exec_execute_C_LDSP. Qed.

  (* +0xd2  7c02  ld s8,32(sp) *)
  Lemma pwi_d2 : kernel_text -∗ instr (mword_of_int (PW + 0xd2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PW + 0xd2)%Z (mword_of_int 0x7c02 : mword 16)
    (mword_of_int (PW + 0xd2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) pwdc_7c02 exec_execute_C_LDSP. Qed.

  (* +0xd4  6ce2  ld s9,24(sp) *)
  Lemma pwi_d4 : kernel_text -∗ instr (mword_of_int (PW + 0xd4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (PW + 0xd4)%Z (mword_of_int 0x6ce2 : mword 16)
    (mword_of_int (PW + 0xd4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) pwdc_6ce2 exec_execute_C_LDSP. Qed.

  (* +0xd6  6d42  ld s10,16(sp) *)
  Lemma pwi_d6 : kernel_text -∗ instr (mword_of_int (PW + 0xd6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (PW + 0xd6)%Z (mword_of_int 0x6d42 : mword 16)
    (mword_of_int (PW + 0xd6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) pwdc_6d42 exec_execute_C_LDSP. Qed.

  (* +0xd8  21848513  addi a0,s1,536 *)
  Lemma pwi_d8 : kernel_text -∗ instr (mword_of_int (PW + 0xd8) : mword 64) false (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PW + 0xd8)%Z (mword_of_int 0x21848513 : mword 32)
    (mword_of_int (PW + 0xd8) : mword 64) (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_21848513. Qed.

  (* +0xdc  9d9fd0ef  jal 80001f52 <wakeup> *)
  Lemma pwi_dc : kernel_text -∗ instr (mword_of_int (PW + 0xdc) : mword 64) false (JAL (mword_of_int 2087384 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0xdc)%Z (mword_of_int 0x9d9fd0ef : mword 32)
    (mword_of_int (PW + 0xdc) : mword 64) (JAL (mword_of_int 2087384 : mword 21, Regidx (mword_of_int 1))) pwdb_9d9fd0ef. Qed.

  (* +0xe0  8526  mv a0,s1 *)
  Lemma pwi_e0 : kernel_text -∗ instr (mword_of_int (PW + 0xe0) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PW + 0xe0)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PW + 0xe0) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0xe2  f10fc0ef  jal 80000c90 <release> *)
  Lemma pwi_e2 : kernel_text -∗ instr (mword_of_int (PW + 0xe2) : mword 64) false (JAL (mword_of_int 2082576 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PW + 0xe2)%Z (mword_of_int 0xf10fc0ef : mword 32)
    (mword_of_int (PW + 0xe2) : mword 64) (JAL (mword_of_int 2082576 : mword 21, Regidx (mword_of_int 1))) pwdb_f10fc0ef. Qed.

  (* +0xe6  bf8d  j 800044f6 <pipewrite+0x58> *)
  Lemma pwi_e6 : kernel_text -∗ instr (mword_of_int (PW + 0xe6) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1977 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PW + 0xe6)%Z (mword_of_int 0xbf8d : mword 16)
    (mword_of_int (PW + 0xe6) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1977 : mword 11) ('b"0")), zreg)) pwdc_bf8d exec_execute_C_J. Qed.

  (* +0xe8  4901  li s2,0 *)
  Lemma pwi_e8 : kernel_text -∗ instr (mword_of_int (PW + 0xe8) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (PW + 0xe8)%Z (mword_of_int 0x4901 : mword 16)
    (mword_of_int (PW + 0xe8) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)) cdec_4901 exec_execute_C_LI. Qed.

  (* +0xea  b7fd  j 80004576 <pipewrite+0xd8> *)
  Lemma pwi_ea : kernel_text -∗ instr (mword_of_int (PW + 0xea) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PW + 0xea)%Z (mword_of_int 0xb7fd : mword 16)
    (mword_of_int (PW + 0xea) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)) cdec_b7fd exec_execute_C_J. Qed.

  (* +0xec  7b42  ld s6,48(sp) *)
  Lemma pwi_ec : kernel_text -∗ instr (mword_of_int (PW + 0xec) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PW + 0xec)%Z (mword_of_int 0x7b42 : mword 16)
    (mword_of_int (PW + 0xec) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) pwdc_7b42 exec_execute_C_LDSP. Qed.

  (* +0xee  7ba2  ld s7,40(sp) *)
  Lemma pwi_ee : kernel_text -∗ instr (mword_of_int (PW + 0xee) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PW + 0xee)%Z (mword_of_int 0x7ba2 : mword 16)
    (mword_of_int (PW + 0xee) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) pwdc_7ba2 exec_execute_C_LDSP. Qed.

  (* +0xf0  7c02  ld s8,32(sp) *)
  Lemma pwi_f0 : kernel_text -∗ instr (mword_of_int (PW + 0xf0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PW + 0xf0)%Z (mword_of_int 0x7c02 : mword 16)
    (mword_of_int (PW + 0xf0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) pwdc_7c02 exec_execute_C_LDSP. Qed.

  (* +0xf2  6ce2  ld s9,24(sp) *)
  Lemma pwi_f2 : kernel_text -∗ instr (mword_of_int (PW + 0xf2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (PW + 0xf2)%Z (mword_of_int 0x6ce2 : mword 16)
    (mword_of_int (PW + 0xf2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) pwdc_6ce2 exec_execute_C_LDSP. Qed.

  (* +0xf4  6d42  ld s10,16(sp) *)
  Lemma pwi_f4 : kernel_text -∗ instr (mword_of_int (PW + 0xf4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (PW + 0xf4)%Z (mword_of_int 0x6d42 : mword 16)
    (mword_of_int (PW + 0xf4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) pwdc_6d42 exec_execute_C_LDSP. Qed.

  (* +0xf6  b7cd  j 80004576 <pipewrite+0xd8> *)
  Lemma pwi_f6 : kernel_text -∗ instr (mword_of_int (PW + 0xf6) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PW + 0xf6)%Z (mword_of_int 0xb7cd : mword 16)
    (mword_of_int (PW + 0xf6) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)) cdec_b7cd exec_execute_C_J. Qed.

End PipewriteInstrs.

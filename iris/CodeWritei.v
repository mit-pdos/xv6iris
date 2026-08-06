(* CodeWritei.v -- the instruction-DECODE layer for xv6's writei().
   For EVERY instruction of

     writei @ 0x80003652 .. 0x80003750   (offsets 0x000 .. 0x0fe, 256 bytes,
                                          98 instructions)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([wri_<off>]) plus
   the per-word decode facts they consume ([wrdc_<word>] compressed /
   [wrdb_<word>] base / [wrcx_<word>] the compressed load expansion).

   writei(ip, user_src, src, off, n) copies n bytes into the inode's file
   data, one block at a time, and grows ip->size.  Frame: 112 bytes; ra, s0,
   s2, s4, s5, s6, s7 are pushed unconditionally, s3 and then s1/s8/s9/s10/s11
   only after the bounds checks pass.  The early bounds check at +0x000 runs
   BEFORE the frame exists and exits through a bare [li a0,-1; ret] at +0x0f8.
   The loop BODY (+0x04c..+0x07e) precedes the loop HEAD (+0x082..+0x0ae) in
   address order.

   Byte-exact disassembly, taken from the tracked kernel-rocq/KernelInstrs.v
   (never from a rebuilt ELF):

     0x000 457c     c.lw a5,76(a0)        -- a5 := ip->size
     0x002 0ed7eb63 bltu a5,a3,8000374a [+0xf8]
     0x006 7159     addi sp,sp,-112
     0x008 f486     sd ra,104(sp)
     0x00a f0a2     sd s0,96(sp)
     0x00c e8ca     sd s2,80(sp)
     0x00e e0d2     sd s4,64(sp)
     0x010 fc56     sd s5,56(sp)
     0x012 f85a     sd s6,48(sp)
     0x014 f45e     sd s7,40(sp)
     0x016 1880     addi s0,sp,112
     0x018 8aaa     mv s5,a0
     0x01a 8bae     mv s7,a1
     0x01c 8a32     mv s4,a2
     0x01e 8936     mv s2,a3
     0x020 8b3a     mv s6,a4
     0x022 00e687bb addw a5,a3,a4
     0x026 00043737 lui a4,0x43
     0x02a 0cf76963 bltu a4,a5,8000374e [+0xfc]
     0x02e 0cd7e763 bltu a5,a3,8000374e [+0xfc]
     0x032 e4ce     sd s3,72(sp)
     0x034 0a0b0a63 beqz s6,8000373a [+0xe8]
     0x038 eca6     sd s1,88(sp)
     0x03a f062     sd s8,32(sp)
     0x03c ec66     sd s9,24(sp)
     0x03e e86a     sd s10,16(sp)
     0x040 e46e     sd s11,8(sp)
     0x042 4981     li s3,0
     0x044 40000c93 li s9,1024
     0x048 5c7d     li s8,-1
     0x04a a825     j 800036d4 [+0x82]
     0x04c 020d1d93 slli s11,s10,0x20
     0x050 020ddd93 srli s11,s11,0x20
     0x054 05848513 addi a0,s1,88
     0x058 86ee     mv a3,s11
     0x05a 8652     mv a2,s4
     0x05c 85de     mv a1,s7
     0x05e 953e     add a0,a0,a5
     0x060 bf9fe0ef jal 800022aa [either_copyin]
     0x064 05850663 beq a0,s8,80003702 [+0xb0]
     0x068 8526     mv a0,s1
     0x06a 6b0000ef jal 80003d6c [log_write]
     0x06e 8526     mv a0,s1
     0x070 d7cff0ef jal 80002c3e [brelse]
     0x074 013d09bb addw s3,s10,s3
     0x078 012d093b addw s2,s10,s2
     0x07c 9a6e     add s4,s4,s11
     0x07e 0369fc63 bgeu s3,s6,80003708 [+0xb6]
     0x082 00a9559b srliw a1,s2,0xa
     0x086 8556     mv a0,s5
     0x088 fc2ff0ef jal 80002e9c [bmap]
     0x08c 85aa     mv a1,a0
     0x08e c505     beqz a0,80003708 [+0xb6]
     0x090 000aa503 lw a0,0(s5)
     0x094 c50ff0ef jal 80002b36 [bread]
     0x098 84aa     mv s1,a0
     0x09a 3ff97793 andi a5,s2,1023
     0x09e 40fc873b subw a4,s9,a5
     0x0a2 413b06bb subw a3,s6,s3
     0x0a6 8d3a     mv s10,a4
     0x0a8 fae6f2e3 bgeu a3,a4,8000369e [+0x4c]
     0x0ac 8d36     mv s10,a3
     0x0ae bf79     j 8000369e [+0x4c]
     0x0b0 8526     mv a0,s1
     0x0b2 d3aff0ef jal 80002c3e [brelse]
     0x0b6 04caa783 lw a5,76(s5)
     0x0ba 0327f963 bgeu a5,s2,8000373e [+0xec]
     0x0be 052aa623 sw s2,76(s5)
     0x0c2 64e6     ld s1,88(sp)
     0x0c4 7c02     ld s8,32(sp)
     0x0c6 6ce2     ld s9,24(sp)
     0x0c8 6d42     ld s10,16(sp)
     0x0ca 6da2     ld s11,8(sp)
     0x0cc 8556     mv a0,s5
     0x0ce 9fbff0ef jal 8000311a [iupdate]
     0x0d2 854e     mv a0,s3
     0x0d4 69a6     ld s3,72(sp)
     0x0d6 70a6     ld ra,104(sp)
     0x0d8 7406     ld s0,96(sp)
     0x0da 6946     ld s2,80(sp)
     0x0dc 6a06     ld s4,64(sp)
     0x0de 7ae2     ld s5,56(sp)
     0x0e0 7b42     ld s6,48(sp)
     0x0e2 7ba2     ld s7,40(sp)
     0x0e4 6165     addi sp,sp,112
     0x0e6 8082     ret
     0x0e8 89da     mv s3,s6
     0x0ea b7cd     j 8000371e [+0xcc]
     0x0ec 64e6     ld s1,88(sp)
     0x0ee 7c02     ld s8,32(sp)
     0x0f0 6ce2     ld s9,24(sp)
     0x0f2 6d42     ld s10,16(sp)
     0x0f4 6da2     ld s11,8(sp)
     0x0f6 bfd9     j 8000371e [+0xcc]
     0x0f8 557d     li a0,-1
     0x0fa 8082     ret
     0x0fc 557d     li a0,-1
     0x0fe bfe1     j 80003728 [+0xd6]

   Offsets tile all 256 bytes with no gap and no overlap (checked against the
   MkKInstr table in kernel-rocq/KernelInstrs.v).  Note the ENTRY instruction
   at +0x000 carries only the symbol comment [<writei> @ 0x80003652] in that
   table, not a disassembly line: 98 instructions, not 97.

   SHARED WORDS.  Fourteen of writei's fifty-eight distinct compressed
   encodings already have a proof in KernelRvcDecode.v and are NOT re-proved
   here (the dedup rule in claude-notes/durable-notes.md): the moves 0x8aaa /
   0x8a32 / 0x8526 / 0x8556 / 0x85aa / 0x84aa / 0x854e, the adds 0x953e, the
   [li] words 0x4981 / 0x557d, the jumps 0xb7cd / 0xbfd9 / 0xbfe1, and 0x8082
   (c.ret).  The other forty-four are proved below.

   None of writei's thirty distinct BASE words is in KernelBaseDecode.v, so
   all thirty are proved here.

   DEDUP SWEEP OWED.  Thirty-two of the words proved privately below already
   have a private copy in another function's Code file, and by the altitude
   rule they belong in the shared catalogues -- but a Code file must never
   import another Code file, so moving them down is a separate sweep, not
   something this file can do:
     the whole 112-byte frame, all in CodePipewrite.v:
       0x7159 0xf486 0xf0a2 0xe8ca 0xe0d2 0xfc56 0xf85a 0xf45e 0x1880
       0xe4ce 0xeca6 0xf062 0xec66 0xe86a
       0x64e6 0x7c02 0x6ce2 0x6d42 0x69a6 0x70a6 0x7406 0x6946 0x6a06
       0x7ae2 0x7b42 0x7ba2 0x6165
     0x8bae     c.mv s7,a1        also in CodeUvmcopy.v
     0x8652     c.mv a2,s4        also in CodeUvmcopy.v
     0x8936     c.mv s2,a3        also in CodeEitherCopy.v
     0x5c7d     c.li s8,-1        also in CodeVirtioDiskRw.v
     0x05848513 addi a0,s1,88     also in CodeEndOp.v
   (writei's own 112-byte frame differs from pipewrite's only by the two
   s11/s10 slots 0xe46e / 0x6da2, which are new to the tree.)                *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts private to writei.                             *)
(* ===================================================================== *)

(* 0x457c  c.lw a5,76(a0) *)
Lemma wrdc_457c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x457c : mword 16)) s
  = Some (C_LW (mword_of_int 19, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7159  addi sp,sp,-112 *)
Lemma wrdc_7159 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7159 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 57 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf486  sd ra,104(sp) *)
Lemma wrdc_f486 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf486 : mword 16)) s
  = Some (C_SDSP (mword_of_int 13, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf0a2  sd s0,96(sp) *)
Lemma wrdc_f0a2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0a2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 12, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe8ca  sd s2,80(sp) *)
Lemma wrdc_e8ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8ca : mword 16)) s
  = Some (C_SDSP (mword_of_int 10, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe0d2  sd s4,64(sp) *)
Lemma wrdc_e0d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe0d2 : mword 16)) s
  = Some (C_SDSP (mword_of_int 8, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xfc56  sd s5,56(sp) *)
Lemma wrdc_fc56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc56 : mword 16)) s
  = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf85a  sd s6,48(sp) *)
Lemma wrdc_f85a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf85a : mword 16)) s
  = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf45e  sd s7,40(sp) *)
Lemma wrdc_f45e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf45e : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1880  addi s0,sp,112 *)
Lemma wrdc_1880 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x1880 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 28 : mword 8), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8bae  mv s7,a1 *)
Lemma wrdc_8bae s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8bae : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 23), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8936  mv s2,a3 *)
Lemma wrdc_8936 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8936 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8b3a  mv s6,a4 *)
Lemma wrdc_8b3a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b3a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 22), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe4ce  sd s3,72(sp) *)
Lemma wrdc_e4ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe4ce : mword 16)) s
  = Some (C_SDSP (mword_of_int 9, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xeca6  sd s1,88(sp) *)
Lemma wrdc_eca6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeca6 : mword 16)) s
  = Some (C_SDSP (mword_of_int 11, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xf062  sd s8,32(sp) *)
Lemma wrdc_f062 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf062 : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xec66  sd s9,24(sp) *)
Lemma wrdc_ec66 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec66 : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe86a  sd s10,16(sp) *)
Lemma wrdc_e86a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe86a : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe46e  sd s11,8(sp) *)
Lemma wrdc_e46e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe46e : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x5c7d  li s8,-1 *)
Lemma wrdc_5c7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5c7d : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa825  j 800036d4 <writei+0x82> *)
Lemma wrdc_a825 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa825 : mword 16)) s
  = Some (C_J (mword_of_int 28 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x86ee  mv a3,s11 *)
Lemma wrdc_86ee s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86ee : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8652  mv a2,s4 *)
Lemma wrdc_8652 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8652 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x85de  mv a1,s7 *)
Lemma wrdc_85de s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85de : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9a6e  add s4,s4,s11 *)
Lemma wrdc_9a6e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9a6e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 20), Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc505  beqz a0,80003708 <writei+0xb6> *)
Lemma wrdc_c505 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc505 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 20, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8d3a  mv s10,a4 *)
Lemma wrdc_8d3a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8d3a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 26), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8d36  mv s10,a3 *)
Lemma wrdc_8d36 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8d36 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 26), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbf79  j 8000369e <writei+0x4c> *)
Lemma wrdc_bf79 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf79 : mword 16)) s
  = Some (C_J (mword_of_int 1999 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64e6  ld s1,88(sp) *)
Lemma wrdc_64e6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64e6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 11, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7c02  ld s8,32(sp) *)
Lemma wrdc_7c02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7c02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6ce2  ld s9,24(sp) *)
Lemma wrdc_6ce2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6ce2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6d42  ld s10,16(sp) *)
Lemma wrdc_6d42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6d42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6da2  ld s11,8(sp) *)
Lemma wrdc_6da2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6da2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 27)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x69a6  ld s3,72(sp) *)
Lemma wrdc_69a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69a6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 9, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70a6  ld ra,104(sp) *)
Lemma wrdc_70a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70a6 : mword 16)) s
  = Some (C_LDSP (mword_of_int 13, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7406  ld s0,96(sp) *)
Lemma wrdc_7406 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7406 : mword 16)) s
  = Some (C_LDSP (mword_of_int 12, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6946  ld s2,80(sp) *)
Lemma wrdc_6946 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6946 : mword 16)) s
  = Some (C_LDSP (mword_of_int 10, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6a06  ld s4,64(sp) *)
Lemma wrdc_6a06 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a06 : mword 16)) s
  = Some (C_LDSP (mword_of_int 8, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7ae2  ld s5,56(sp) *)
Lemma wrdc_7ae2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ae2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7b42  ld s6,48(sp) *)
Lemma wrdc_7b42 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7b42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7ba2  ld s7,40(sp) *)
Lemma wrdc_7ba2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7ba2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6165  addi sp,sp,112 *)
Lemma wrdc_6165 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6165 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 7 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x89da  mv s3,s6 *)
Lemma wrdc_89da s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89da : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansion of the one compressed load: a literal
   [mword 12] displacement and plain [Regidx]es, which is the shape the WP
   load leaf takes. ---- *)

Lemma wrcx_457c s :
  exec (execute (C_LW (mword_of_int 19, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 76, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* bltu a5,a3,8000374a <writei+0xf8> *)
Lemma wrdb_0ed7eb63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ed7eb63 : mword 32)) s
  = Some (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* addw a5,a3,a4 *)
Lemma wrdb_00e687bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e687bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 14), Regidx (mword_of_int 13), Regidx (mword_of_int 15), ADDW), s).
Proof. decode_bridge_ms. Qed.

(* lui a4,0x43 *)
Lemma wrdb_00043737 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00043737 : mword 32)) s
  = Some (UTYPE (mword_of_int 67 : mword 20, Regidx (mword_of_int 14), LUI), s).
Proof. decode_bridge_ms. Qed.

(* bltu a4,a5,8000374e <writei+0xfc> *)
Lemma wrdb_0cf76963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0cf76963 : mword 32)) s
  = Some (BTYPE (mword_of_int 210 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* bltu a5,a3,8000374e <writei+0xfc> *)
Lemma wrdb_0cd7e763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0cd7e763 : mword 32)) s
  = Some (BTYPE (mword_of_int 206 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* beqz s6,8000373a <writei+0xe8> *)
Lemma wrdb_0a0b0a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0a0b0a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 180 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* li s9,1024 *)
Lemma wrdb_40000c93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40000c93 : mword 32)) s
  = Some (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 25), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* slli s11,s10,0x20 *)
Lemma wrdb_020d1d93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020d1d93 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 26), Regidx (mword_of_int 27), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* srli s11,s11,0x20 *)
Lemma wrdb_020ddd93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020ddd93 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 27), Regidx (mword_of_int 27), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,s1,88 *)
Lemma wrdb_05848513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05848513 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* jal 800022aa <either_copyin> *)
Lemma wrdb_bf9fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbf9fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092024 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* beq a0,s8,80003702 <writei+0xb0> *)
Lemma wrdb_05850663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05850663 : mword 32)) s
  = Some (BTYPE (mword_of_int 76 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* jal 80003d6c <log_write> *)
Lemma wrdb_6b0000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6b0000ef : mword 32)) s
  = Some (JAL (mword_of_int 1712 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* jal 80002c3e <brelse> *)
Lemma wrdb_d7cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd7cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094460 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* addw s3,s10,s3 *)
Lemma wrdb_013d09bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x013d09bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 26), Regidx (mword_of_int 19), ADDW), s).
Proof. decode_bridge_ms. Qed.

(* addw s2,s10,s2 *)
Lemma wrdb_012d093b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x012d093b : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 26), Regidx (mword_of_int 18), ADDW), s).
Proof. decode_bridge_ms. Qed.

(* bgeu s3,s6,80003708 <writei+0xb6> *)
Lemma wrdb_0369fc63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0369fc63 : mword 32)) s
  = Some (BTYPE (mword_of_int 56 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 19), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* srliw a1,s2,0xa *)
Lemma wrdb_00a9559b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a9559b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 10 : mword 5, Regidx (mword_of_int 18), Regidx (mword_of_int 11), SRLIW), s).
Proof. decode_bridge_ms. Qed.

(* jal 80002e9c <bmap> *)
Lemma wrdb_fc2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095042 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* lw a0,0(s5) *)
Lemma wrdb_000aa503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000aa503 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* jal 80002b36 <bread> *)
Lemma wrdb_c50ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc50ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094160 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* andi a5,s2,1023 *)
Lemma wrdb_3ff97793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x3ff97793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* subw a4,s9,a5 *)
Lemma wrdb_40fc873b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40fc873b : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 25), Regidx (mword_of_int 14), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* subw a3,s6,s3 *)
Lemma wrdb_413b06bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x413b06bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 22), Regidx (mword_of_int 13), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* bgeu a3,a4,8000369e <writei+0x4c> *)
Lemma wrdb_fae6f2e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfae6f2e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8100 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* jal 80002c3e <brelse> *)
Lemma wrdb_d3aff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd3aff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094394 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* lw a5,76(s5) *)
Lemma wrdb_04caa783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04caa783 : mword 32)) s
  = Some (LOAD (mword_of_int 76 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* bgeu a5,s2,8000373e <writei+0xec> *)
Lemma wrdb_0327f963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0327f963 : mword 32)) s
  = Some (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* sw s2,76(s5) *)
Lemma wrdb_052aa623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x052aa623 : mword 32)) s
  = Some (STORE (mword_of_int 76 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 21), 4), s).
Proof. decode_bridge_ms. Qed.

(* jal 8000311a <iupdate> *)
Lemma wrdb_9fbff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9fbff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095610 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section WriteiInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation WR := KernelSyms.writei.

  (* 0x457c  c.lw a5,76(a0) *)
  Lemma wri_00 : kernel_text -∗ instr (mword_of_int (WR + 0x00) : mword 64) true (LOAD (mword_of_int 76, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (WR + 0x00)%Z (mword_of_int 0x457c : mword 16)
    (mword_of_int (WR + 0x00) : mword 64) (LOAD (mword_of_int 76, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 4)) wrdc_457c wrcx_457c. Qed.

  (* bltu a5,a3,8000374a [+0xf8] *)
  Lemma wri_02 : kernel_text -∗ instr (mword_of_int (WR + 0x02) : mword 64) false (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (WR + 0x02)%Z (mword_of_int 0x0ed7eb63 : mword 32)
    (mword_of_int (WR + 0x02) : mword 64) (BTYPE (mword_of_int 246 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU)) wrdb_0ed7eb63. Qed.

  (* 0x7159  addi sp,sp,-112 *)
  Lemma wri_06 : kernel_text -∗ instr (mword_of_int (WR + 0x06) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 57 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (WR + 0x06)%Z (mword_of_int 0x7159 : mword 16)
    (mword_of_int (WR + 0x06) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 57 : mword 6), sp, sp, ADDI)) wrdc_7159 exec_execute_C_ADDI16SP. Qed.

  (* 0xf486  sd ra,104(sp) *)
  Lemma wri_08 : kernel_text -∗ instr (mword_of_int (WR + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (WR + 0x08)%Z (mword_of_int 0xf486 : mword 16)
    (mword_of_int (WR + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) wrdc_f486 exec_execute_C_SDSP. Qed.

  (* 0xf0a2  sd s0,96(sp) *)
  Lemma wri_0a : kernel_text -∗ instr (mword_of_int (WR + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (WR + 0x0a)%Z (mword_of_int 0xf0a2 : mword 16)
    (mword_of_int (WR + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) wrdc_f0a2 exec_execute_C_SDSP. Qed.

  (* 0xe8ca  sd s2,80(sp) *)
  Lemma wri_0c : kernel_text -∗ instr (mword_of_int (WR + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (WR + 0x0c)%Z (mword_of_int 0xe8ca : mword 16)
    (mword_of_int (WR + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) wrdc_e8ca exec_execute_C_SDSP. Qed.

  (* 0xe0d2  sd s4,64(sp) *)
  Lemma wri_0e : kernel_text -∗ instr (mword_of_int (WR + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (WR + 0x0e)%Z (mword_of_int 0xe0d2 : mword 16)
    (mword_of_int (WR + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) wrdc_e0d2 exec_execute_C_SDSP. Qed.

  (* 0xfc56  sd s5,56(sp) *)
  Lemma wri_10 : kernel_text -∗ instr (mword_of_int (WR + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (WR + 0x10)%Z (mword_of_int 0xfc56 : mword 16)
    (mword_of_int (WR + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) wrdc_fc56 exec_execute_C_SDSP. Qed.

  (* 0xf85a  sd s6,48(sp) *)
  Lemma wri_12 : kernel_text -∗ instr (mword_of_int (WR + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (WR + 0x12)%Z (mword_of_int 0xf85a : mword 16)
    (mword_of_int (WR + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) wrdc_f85a exec_execute_C_SDSP. Qed.

  (* 0xf45e  sd s7,40(sp) *)
  Lemma wri_14 : kernel_text -∗ instr (mword_of_int (WR + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (WR + 0x14)%Z (mword_of_int 0xf45e : mword 16)
    (mword_of_int (WR + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) wrdc_f45e exec_execute_C_SDSP. Qed.

  (* 0x1880  addi s0,sp,112 *)
  Lemma wri_16 : kernel_text -∗ instr (mword_of_int (WR + 0x16) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 28 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (WR + 0x16)%Z (mword_of_int 0x1880 : mword 16)
    (mword_of_int (WR + 0x16) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 28 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) wrdc_1880 exec_execute_C_ADDI4SPN. Qed.

  (* 0x8aaa  mv s5,a0 *)
  Lemma wri_18 : kernel_text -∗ instr (mword_of_int (WR + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (WR + 0x18)%Z (mword_of_int 0x8aaa : mword 16)
    (mword_of_int (WR + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)) cdec_8aaa exec_execute_C_MV. Qed.

  (* 0x8bae  mv s7,a1 *)
  Lemma wri_1a : kernel_text -∗ instr (mword_of_int (WR + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 23), ADD)).
  Proof. mk_rvc (WR + 0x1a)%Z (mword_of_int 0x8bae : mword 16)
    (mword_of_int (WR + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 23), ADD)) wrdc_8bae exec_execute_C_MV. Qed.

  (* 0x8a32  mv s4,a2 *)
  Lemma wri_1c : kernel_text -∗ instr (mword_of_int (WR + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (WR + 0x1c)%Z (mword_of_int 0x8a32 : mword 16)
    (mword_of_int (WR + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a32 exec_execute_C_MV. Qed.

  (* 0x8936  mv s2,a3 *)
  Lemma wri_1e : kernel_text -∗ instr (mword_of_int (WR + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (WR + 0x1e)%Z (mword_of_int 0x8936 : mword 16)
    (mword_of_int (WR + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 18), ADD)) wrdc_8936 exec_execute_C_MV. Qed.

  (* 0x8b3a  mv s6,a4 *)
  Lemma wri_20 : kernel_text -∗ instr (mword_of_int (WR + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (WR + 0x20)%Z (mword_of_int 0x8b3a : mword 16)
    (mword_of_int (WR + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 22), ADD)) wrdc_8b3a exec_execute_C_MV. Qed.

  (* addw a5,a3,a4 *)
  Lemma wri_22 : kernel_text -∗ instr (mword_of_int (WR + 0x22) : mword 64) false (RTYPEW (Regidx (mword_of_int 14), Regidx (mword_of_int 13), Regidx (mword_of_int 15), ADDW)).
  Proof. mk_base (WR + 0x22)%Z (mword_of_int 0x00e687bb : mword 32)
    (mword_of_int (WR + 0x22) : mword 64) (RTYPEW (Regidx (mword_of_int 14), Regidx (mword_of_int 13), Regidx (mword_of_int 15), ADDW)) wrdb_00e687bb. Qed.

  (* lui a4,0x43 *)
  Lemma wri_26 : kernel_text -∗ instr (mword_of_int (WR + 0x26) : mword 64) false (UTYPE (mword_of_int 67 : mword 20, Regidx (mword_of_int 14), LUI)).
  Proof. mk_base (WR + 0x26)%Z (mword_of_int 0x00043737 : mword 32)
    (mword_of_int (WR + 0x26) : mword 64) (UTYPE (mword_of_int 67 : mword 20, Regidx (mword_of_int 14), LUI)) wrdb_00043737. Qed.

  (* bltu a4,a5,8000374e [+0xfc] *)
  Lemma wri_2a : kernel_text -∗ instr (mword_of_int (WR + 0x2a) : mword 64) false (BTYPE (mword_of_int 210 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)).
  Proof. mk_base (WR + 0x2a)%Z (mword_of_int 0x0cf76963 : mword 32)
    (mword_of_int (WR + 0x2a) : mword 64) (BTYPE (mword_of_int 210 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)) wrdb_0cf76963. Qed.

  (* bltu a5,a3,8000374e [+0xfc] *)
  Lemma wri_2e : kernel_text -∗ instr (mword_of_int (WR + 0x2e) : mword 64) false (BTYPE (mword_of_int 206 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (WR + 0x2e)%Z (mword_of_int 0x0cd7e763 : mword 32)
    (mword_of_int (WR + 0x2e) : mword 64) (BTYPE (mword_of_int 206 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BLTU)) wrdb_0cd7e763. Qed.

  (* 0xe4ce  sd s3,72(sp) *)
  Lemma wri_32 : kernel_text -∗ instr (mword_of_int (WR + 0x32) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (WR + 0x32)%Z (mword_of_int 0xe4ce : mword 16)
    (mword_of_int (WR + 0x32) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) wrdc_e4ce exec_execute_C_SDSP. Qed.

  (* beqz s6,8000373a [+0xe8] *)
  Lemma wri_34 : kernel_text -∗ instr (mword_of_int (WR + 0x34) : mword 64) false (BTYPE (mword_of_int 180 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BEQ)).
  Proof. mk_base (WR + 0x34)%Z (mword_of_int 0x0a0b0a63 : mword 32)
    (mword_of_int (WR + 0x34) : mword 64) (BTYPE (mword_of_int 180 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BEQ)) wrdb_0a0b0a63. Qed.

  (* 0xeca6  sd s1,88(sp) *)
  Lemma wri_38 : kernel_text -∗ instr (mword_of_int (WR + 0x38) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (WR + 0x38)%Z (mword_of_int 0xeca6 : mword 16)
    (mword_of_int (WR + 0x38) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) wrdc_eca6 exec_execute_C_SDSP. Qed.

  (* 0xf062  sd s8,32(sp) *)
  Lemma wri_3a : kernel_text -∗ instr (mword_of_int (WR + 0x3a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (WR + 0x3a)%Z (mword_of_int 0xf062 : mword 16)
    (mword_of_int (WR + 0x3a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) wrdc_f062 exec_execute_C_SDSP. Qed.

  (* 0xec66  sd s9,24(sp) *)
  Lemma wri_3c : kernel_text -∗ instr (mword_of_int (WR + 0x3c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)).
  Proof. mk_rvc (WR + 0x3c)%Z (mword_of_int 0xec66 : mword 16)
    (mword_of_int (WR + 0x3c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)) wrdc_ec66 exec_execute_C_SDSP. Qed.

  (* 0xe86a  sd s10,16(sp) *)
  Lemma wri_3e : kernel_text -∗ instr (mword_of_int (WR + 0x3e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)).
  Proof. mk_rvc (WR + 0x3e)%Z (mword_of_int 0xe86a : mword 16)
    (mword_of_int (WR + 0x3e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)) wrdc_e86a exec_execute_C_SDSP. Qed.

  (* 0xe46e  sd s11,8(sp) *)
  Lemma wri_40 : kernel_text -∗ instr (mword_of_int (WR + 0x40) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 27), sp, 8)).
  Proof. mk_rvc (WR + 0x40)%Z (mword_of_int 0xe46e : mword 16)
    (mword_of_int (WR + 0x40) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 27), sp, 8)) wrdc_e46e exec_execute_C_SDSP. Qed.

  (* 0x4981  li s3,0 *)
  Lemma wri_42 : kernel_text -∗ instr (mword_of_int (WR + 0x42) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (WR + 0x42)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (WR + 0x42) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  (* li s9,1024 *)
  Lemma wri_44 : kernel_text -∗ instr (mword_of_int (WR + 0x44) : mword 64) false (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 25), ADDI)).
  Proof. mk_base (WR + 0x44)%Z (mword_of_int 0x40000c93 : mword 32)
    (mword_of_int (WR + 0x44) : mword 64) (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 25), ADDI)) wrdb_40000c93. Qed.

  (* 0x5c7d  li s8,-1 *)
  Lemma wri_48 : kernel_text -∗ instr (mword_of_int (WR + 0x48) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)).
  Proof. mk_rvc (WR + 0x48)%Z (mword_of_int 0x5c7d : mword 16)
    (mword_of_int (WR + 0x48) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)) wrdc_5c7d exec_execute_C_LI. Qed.

  (* 0xa825  j 800036d4 [+0x82] *)
  Lemma wri_4a : kernel_text -∗ instr (mword_of_int (WR + 0x4a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 28 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WR + 0x4a)%Z (mword_of_int 0xa825 : mword 16)
    (mword_of_int (WR + 0x4a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 28 : mword 11) ('b"0")), zreg)) wrdc_a825 exec_execute_C_J. Qed.

  (* slli s11,s10,0x20 *)
  Lemma wri_4c : kernel_text -∗ instr (mword_of_int (WR + 0x4c) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 26), Regidx (mword_of_int 27), SLLI)).
  Proof. mk_base (WR + 0x4c)%Z (mword_of_int 0x020d1d93 : mword 32)
    (mword_of_int (WR + 0x4c) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 26), Regidx (mword_of_int 27), SLLI)) wrdb_020d1d93. Qed.

  (* srli s11,s11,0x20 *)
  Lemma wri_50 : kernel_text -∗ instr (mword_of_int (WR + 0x50) : mword 64) false (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 27), Regidx (mword_of_int 27), SRLI)).
  Proof. mk_base (WR + 0x50)%Z (mword_of_int 0x020ddd93 : mword 32)
    (mword_of_int (WR + 0x50) : mword 64) (SHIFTIOP (mword_of_int 32 : mword 6, Regidx (mword_of_int 27), Regidx (mword_of_int 27), SRLI)) wrdb_020ddd93. Qed.

  (* addi a0,s1,88 *)
  Lemma wri_54 : kernel_text -∗ instr (mword_of_int (WR + 0x54) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (WR + 0x54)%Z (mword_of_int 0x05848513 : mword 32)
    (mword_of_int (WR + 0x54) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) wrdb_05848513. Qed.

  (* 0x86ee  mv a3,s11 *)
  Lemma wri_58 : kernel_text -∗ instr (mword_of_int (WR + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 27), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (WR + 0x58)%Z (mword_of_int 0x86ee : mword 16)
    (mword_of_int (WR + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 27), zreg, Regidx (mword_of_int 13), ADD)) wrdc_86ee exec_execute_C_MV. Qed.

  (* 0x8652  mv a2,s4 *)
  Lemma wri_5a : kernel_text -∗ instr (mword_of_int (WR + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (WR + 0x5a)%Z (mword_of_int 0x8652 : mword 16)
    (mword_of_int (WR + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)) wrdc_8652 exec_execute_C_MV. Qed.

  (* 0x85de  mv a1,s7 *)
  Lemma wri_5c : kernel_text -∗ instr (mword_of_int (WR + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (WR + 0x5c)%Z (mword_of_int 0x85de : mword 16)
    (mword_of_int (WR + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 11), ADD)) wrdc_85de exec_execute_C_MV. Qed.

  (* 0x953e  add a0,a0,a5 *)
  Lemma wri_5e : kernel_text -∗ instr (mword_of_int (WR + 0x5e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0x5e)%Z (mword_of_int 0x953e : mword 16)
    (mword_of_int (WR + 0x5e) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) cdec_953e exec_execute_C_ADD. Qed.

  (* jal 800022aa [either_copyin] *)
  Lemma wri_60 : kernel_text -∗ instr (mword_of_int (WR + 0x60) : mword 64) false (JAL (mword_of_int 2092024 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0x60)%Z (mword_of_int 0xbf9fe0ef : mword 32)
    (mword_of_int (WR + 0x60) : mword 64) (JAL (mword_of_int 2092024 : mword 21, Regidx (mword_of_int 1))) wrdb_bf9fe0ef. Qed.

  (* beq a0,s8,80003702 [+0xb0] *)
  Lemma wri_64 : kernel_text -∗ instr (mword_of_int (WR + 0x64) : mword 64) false (BTYPE (mword_of_int 76 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (WR + 0x64)%Z (mword_of_int 0x05850663 : mword 32)
    (mword_of_int (WR + 0x64) : mword 64) (BTYPE (mword_of_int 76 : mword 13, Regidx (mword_of_int 24), Regidx (mword_of_int 10), BEQ)) wrdb_05850663. Qed.

  (* 0x8526  mv a0,s1 *)
  Lemma wri_68 : kernel_text -∗ instr (mword_of_int (WR + 0x68) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0x68)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (WR + 0x68) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* jal 80003d6c [log_write] *)
  Lemma wri_6a : kernel_text -∗ instr (mword_of_int (WR + 0x6a) : mword 64) false (JAL (mword_of_int 1712 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0x6a)%Z (mword_of_int 0x6b0000ef : mword 32)
    (mword_of_int (WR + 0x6a) : mword 64) (JAL (mword_of_int 1712 : mword 21, Regidx (mword_of_int 1))) wrdb_6b0000ef. Qed.

  (* 0x8526  mv a0,s1 *)
  Lemma wri_6e : kernel_text -∗ instr (mword_of_int (WR + 0x6e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0x6e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (WR + 0x6e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* jal 80002c3e [brelse] *)
  Lemma wri_70 : kernel_text -∗ instr (mword_of_int (WR + 0x70) : mword 64) false (JAL (mword_of_int 2094460 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0x70)%Z (mword_of_int 0xd7cff0ef : mword 32)
    (mword_of_int (WR + 0x70) : mword 64) (JAL (mword_of_int 2094460 : mword 21, Regidx (mword_of_int 1))) wrdb_d7cff0ef. Qed.

  (* addw s3,s10,s3 *)
  Lemma wri_74 : kernel_text -∗ instr (mword_of_int (WR + 0x74) : mword 64) false (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 26), Regidx (mword_of_int 19), ADDW)).
  Proof. mk_base (WR + 0x74)%Z (mword_of_int 0x013d09bb : mword 32)
    (mword_of_int (WR + 0x74) : mword 64) (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 26), Regidx (mword_of_int 19), ADDW)) wrdb_013d09bb. Qed.

  (* addw s2,s10,s2 *)
  Lemma wri_78 : kernel_text -∗ instr (mword_of_int (WR + 0x78) : mword 64) false (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 26), Regidx (mword_of_int 18), ADDW)).
  Proof. mk_base (WR + 0x78)%Z (mword_of_int 0x012d093b : mword 32)
    (mword_of_int (WR + 0x78) : mword 64) (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 26), Regidx (mword_of_int 18), ADDW)) wrdb_012d093b. Qed.

  (* 0x9a6e  add s4,s4,s11 *)
  Lemma wri_7c : kernel_text -∗ instr (mword_of_int (WR + 0x7c) : mword 64) true (RTYPE (Regidx (mword_of_int 27), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (WR + 0x7c)%Z (mword_of_int 0x9a6e : mword 16)
    (mword_of_int (WR + 0x7c) : mword 64) (RTYPE (Regidx (mword_of_int 27), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADD)) wrdc_9a6e exec_execute_C_ADD. Qed.

  (* bgeu s3,s6,80003708 [+0xb6] *)
  Lemma wri_7e : kernel_text -∗ instr (mword_of_int (WR + 0x7e) : mword 64) false (BTYPE (mword_of_int 56 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 19), BGEU)).
  Proof. mk_base (WR + 0x7e)%Z (mword_of_int 0x0369fc63 : mword 32)
    (mword_of_int (WR + 0x7e) : mword 64) (BTYPE (mword_of_int 56 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 19), BGEU)) wrdb_0369fc63. Qed.

  (* srliw a1,s2,0xa *)
  Lemma wri_82 : kernel_text -∗ instr (mword_of_int (WR + 0x82) : mword 64) false (SHIFTIWOP (mword_of_int 10 : mword 5, Regidx (mword_of_int 18), Regidx (mword_of_int 11), SRLIW)).
  Proof. mk_base (WR + 0x82)%Z (mword_of_int 0x00a9559b : mword 32)
    (mword_of_int (WR + 0x82) : mword 64) (SHIFTIWOP (mword_of_int 10 : mword 5, Regidx (mword_of_int 18), Regidx (mword_of_int 11), SRLIW)) wrdb_00a9559b. Qed.

  (* 0x8556  mv a0,s5 *)
  Lemma wri_86 : kernel_text -∗ instr (mword_of_int (WR + 0x86) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0x86)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (WR + 0x86) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  (* jal 80002e9c [bmap] *)
  Lemma wri_88 : kernel_text -∗ instr (mword_of_int (WR + 0x88) : mword 64) false (JAL (mword_of_int 2095042 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0x88)%Z (mword_of_int 0xfc2ff0ef : mword 32)
    (mword_of_int (WR + 0x88) : mword 64) (JAL (mword_of_int 2095042 : mword 21, Regidx (mword_of_int 1))) wrdb_fc2ff0ef. Qed.

  (* 0x85aa  mv a1,a0 *)
  Lemma wri_8c : kernel_text -∗ instr (mword_of_int (WR + 0x8c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (WR + 0x8c)%Z (mword_of_int 0x85aa : mword 16)
    (mword_of_int (WR + 0x8c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)) cdec_85aa exec_execute_C_MV. Qed.

  (* 0xc505  beqz a0,80003708 [+0xb6] *)
  Lemma wri_8e : kernel_text -∗ instr (mword_of_int (WR + 0x8e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 20 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (WR + 0x8e)%Z (mword_of_int 0xc505 : mword 16)
    (mword_of_int (WR + 0x8e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 20 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) wrdc_c505 exec_execute_C_BEQZ. Qed.

  (* lw a0,0(s5) *)
  Lemma wri_90 : kernel_text -∗ instr (mword_of_int (WR + 0x90) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (WR + 0x90)%Z (mword_of_int 0x000aa503 : mword 32)
    (mword_of_int (WR + 0x90) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 10), false, 4)) wrdb_000aa503. Qed.

  (* jal 80002b36 [bread] *)
  Lemma wri_94 : kernel_text -∗ instr (mword_of_int (WR + 0x94) : mword 64) false (JAL (mword_of_int 2094160 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0x94)%Z (mword_of_int 0xc50ff0ef : mword 32)
    (mword_of_int (WR + 0x94) : mword 64) (JAL (mword_of_int 2094160 : mword 21, Regidx (mword_of_int 1))) wrdb_c50ff0ef. Qed.

  (* 0x84aa  mv s1,a0 *)
  Lemma wri_98 : kernel_text -∗ instr (mword_of_int (WR + 0x98) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (WR + 0x98)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (WR + 0x98) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* andi a5,s2,1023 *)
  Lemma wri_9a : kernel_text -∗ instr (mword_of_int (WR + 0x9a) : mword 64) false (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (WR + 0x9a)%Z (mword_of_int 0x3ff97793 : mword 32)
    (mword_of_int (WR + 0x9a) : mword 64) (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 15), ANDI)) wrdb_3ff97793. Qed.

  (* subw a4,s9,a5 *)
  Lemma wri_9e : kernel_text -∗ instr (mword_of_int (WR + 0x9e) : mword 64) false (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 25), Regidx (mword_of_int 14), SUBW)).
  Proof. mk_base (WR + 0x9e)%Z (mword_of_int 0x40fc873b : mword 32)
    (mword_of_int (WR + 0x9e) : mword 64) (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 25), Regidx (mword_of_int 14), SUBW)) wrdb_40fc873b. Qed.

  (* subw a3,s6,s3 *)
  Lemma wri_a2 : kernel_text -∗ instr (mword_of_int (WR + 0xa2) : mword 64) false (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 22), Regidx (mword_of_int 13), SUBW)).
  Proof. mk_base (WR + 0xa2)%Z (mword_of_int 0x413b06bb : mword 32)
    (mword_of_int (WR + 0xa2) : mword 64) (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 22), Regidx (mword_of_int 13), SUBW)) wrdb_413b06bb. Qed.

  (* 0x8d3a  mv s10,a4 *)
  Lemma wri_a6 : kernel_text -∗ instr (mword_of_int (WR + 0xa6) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 26), ADD)).
  Proof. mk_rvc (WR + 0xa6)%Z (mword_of_int 0x8d3a : mword 16)
    (mword_of_int (WR + 0xa6) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 26), ADD)) wrdc_8d3a exec_execute_C_MV. Qed.

  (* bgeu a3,a4,8000369e [+0x4c] *)
  Lemma wri_a8 : kernel_text -∗ instr (mword_of_int (WR + 0xa8) : mword 64) false (BTYPE (mword_of_int 8100 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BGEU)).
  Proof. mk_base (WR + 0xa8)%Z (mword_of_int 0xfae6f2e3 : mword 32)
    (mword_of_int (WR + 0xa8) : mword 64) (BTYPE (mword_of_int 8100 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 13), BGEU)) wrdb_fae6f2e3. Qed.

  (* 0x8d36  mv s10,a3 *)
  Lemma wri_ac : kernel_text -∗ instr (mword_of_int (WR + 0xac) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 26), ADD)).
  Proof. mk_rvc (WR + 0xac)%Z (mword_of_int 0x8d36 : mword 16)
    (mword_of_int (WR + 0xac) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 26), ADD)) wrdc_8d36 exec_execute_C_MV. Qed.

  (* 0xbf79  j 8000369e [+0x4c] *)
  Lemma wri_ae : kernel_text -∗ instr (mword_of_int (WR + 0xae) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1999 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WR + 0xae)%Z (mword_of_int 0xbf79 : mword 16)
    (mword_of_int (WR + 0xae) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1999 : mword 11) ('b"0")), zreg)) wrdc_bf79 exec_execute_C_J. Qed.

  (* 0x8526  mv a0,s1 *)
  Lemma wri_b0 : kernel_text -∗ instr (mword_of_int (WR + 0xb0) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0xb0)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (WR + 0xb0) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* jal 80002c3e [brelse] *)
  Lemma wri_b2 : kernel_text -∗ instr (mword_of_int (WR + 0xb2) : mword 64) false (JAL (mword_of_int 2094394 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0xb2)%Z (mword_of_int 0xd3aff0ef : mword 32)
    (mword_of_int (WR + 0xb2) : mword 64) (JAL (mword_of_int 2094394 : mword 21, Regidx (mword_of_int 1))) wrdb_d3aff0ef. Qed.

  (* lw a5,76(s5) *)
  Lemma wri_b6 : kernel_text -∗ instr (mword_of_int (WR + 0xb6) : mword 64) false (LOAD (mword_of_int 76 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (WR + 0xb6)%Z (mword_of_int 0x04caa783 : mword 32)
    (mword_of_int (WR + 0xb6) : mword 64) (LOAD (mword_of_int 76 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 15), false, 4)) wrdb_04caa783. Qed.

  (* bgeu a5,s2,8000373e [+0xec] *)
  Lemma wri_ba : kernel_text -∗ instr (mword_of_int (WR + 0xba) : mword 64) false (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGEU)).
  Proof. mk_base (WR + 0xba)%Z (mword_of_int 0x0327f963 : mword 32)
    (mword_of_int (WR + 0xba) : mword 64) (BTYPE (mword_of_int 50 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BGEU)) wrdb_0327f963. Qed.

  (* sw s2,76(s5) *)
  Lemma wri_be : kernel_text -∗ instr (mword_of_int (WR + 0xbe) : mword 64) false (STORE (mword_of_int 76 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 21), 4)).
  Proof. mk_base (WR + 0xbe)%Z (mword_of_int 0x052aa623 : mword 32)
    (mword_of_int (WR + 0xbe) : mword 64) (STORE (mword_of_int 76 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 21), 4)) wrdb_052aa623. Qed.

  (* 0x64e6  ld s1,88(sp) *)
  Lemma wri_c2 : kernel_text -∗ instr (mword_of_int (WR + 0xc2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (WR + 0xc2)%Z (mword_of_int 0x64e6 : mword 16)
    (mword_of_int (WR + 0xc2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) wrdc_64e6 exec_execute_C_LDSP. Qed.

  (* 0x7c02  ld s8,32(sp) *)
  Lemma wri_c4 : kernel_text -∗ instr (mword_of_int (WR + 0xc4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (WR + 0xc4)%Z (mword_of_int 0x7c02 : mword 16)
    (mword_of_int (WR + 0xc4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) wrdc_7c02 exec_execute_C_LDSP. Qed.

  (* 0x6ce2  ld s9,24(sp) *)
  Lemma wri_c6 : kernel_text -∗ instr (mword_of_int (WR + 0xc6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (WR + 0xc6)%Z (mword_of_int 0x6ce2 : mword 16)
    (mword_of_int (WR + 0xc6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) wrdc_6ce2 exec_execute_C_LDSP. Qed.

  (* 0x6d42  ld s10,16(sp) *)
  Lemma wri_c8 : kernel_text -∗ instr (mword_of_int (WR + 0xc8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (WR + 0xc8)%Z (mword_of_int 0x6d42 : mword 16)
    (mword_of_int (WR + 0xc8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) wrdc_6d42 exec_execute_C_LDSP. Qed.

  (* 0x6da2  ld s11,8(sp) *)
  Lemma wri_ca : kernel_text -∗ instr (mword_of_int (WR + 0xca) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)).
  Proof. mk_rvc (WR + 0xca)%Z (mword_of_int 0x6da2 : mword 16)
    (mword_of_int (WR + 0xca) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)) wrdc_6da2 exec_execute_C_LDSP. Qed.

  (* 0x8556  mv a0,s5 *)
  Lemma wri_cc : kernel_text -∗ instr (mword_of_int (WR + 0xcc) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0xcc)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (WR + 0xcc) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  (* jal 8000311a [iupdate] *)
  Lemma wri_ce : kernel_text -∗ instr (mword_of_int (WR + 0xce) : mword 64) false (JAL (mword_of_int 2095610 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WR + 0xce)%Z (mword_of_int 0x9fbff0ef : mword 32)
    (mword_of_int (WR + 0xce) : mword 64) (JAL (mword_of_int 2095610 : mword 21, Regidx (mword_of_int 1))) wrdb_9fbff0ef. Qed.

  (* 0x854e  mv a0,s3 *)
  Lemma wri_d2 : kernel_text -∗ instr (mword_of_int (WR + 0xd2) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WR + 0xd2)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (WR + 0xd2) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  (* 0x69a6  ld s3,72(sp) *)
  Lemma wri_d4 : kernel_text -∗ instr (mword_of_int (WR + 0xd4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (WR + 0xd4)%Z (mword_of_int 0x69a6 : mword 16)
    (mword_of_int (WR + 0xd4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) wrdc_69a6 exec_execute_C_LDSP. Qed.

  (* 0x70a6  ld ra,104(sp) *)
  Lemma wri_d6 : kernel_text -∗ instr (mword_of_int (WR + 0xd6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (WR + 0xd6)%Z (mword_of_int 0x70a6 : mword 16)
    (mword_of_int (WR + 0xd6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 13 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) wrdc_70a6 exec_execute_C_LDSP. Qed.

  (* 0x7406  ld s0,96(sp) *)
  Lemma wri_d8 : kernel_text -∗ instr (mword_of_int (WR + 0xd8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (WR + 0xd8)%Z (mword_of_int 0x7406 : mword 16)
    (mword_of_int (WR + 0xd8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 12 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) wrdc_7406 exec_execute_C_LDSP. Qed.

  (* 0x6946  ld s2,80(sp) *)
  Lemma wri_da : kernel_text -∗ instr (mword_of_int (WR + 0xda) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (WR + 0xda)%Z (mword_of_int 0x6946 : mword 16)
    (mword_of_int (WR + 0xda) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) wrdc_6946 exec_execute_C_LDSP. Qed.

  (* 0x6a06  ld s4,64(sp) *)
  Lemma wri_dc : kernel_text -∗ instr (mword_of_int (WR + 0xdc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (WR + 0xdc)%Z (mword_of_int 0x6a06 : mword 16)
    (mword_of_int (WR + 0xdc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) wrdc_6a06 exec_execute_C_LDSP. Qed.

  (* 0x7ae2  ld s5,56(sp) *)
  Lemma wri_de : kernel_text -∗ instr (mword_of_int (WR + 0xde) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (WR + 0xde)%Z (mword_of_int 0x7ae2 : mword 16)
    (mword_of_int (WR + 0xde) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) wrdc_7ae2 exec_execute_C_LDSP. Qed.

  (* 0x7b42  ld s6,48(sp) *)
  Lemma wri_e0 : kernel_text -∗ instr (mword_of_int (WR + 0xe0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (WR + 0xe0)%Z (mword_of_int 0x7b42 : mword 16)
    (mword_of_int (WR + 0xe0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) wrdc_7b42 exec_execute_C_LDSP. Qed.

  (* 0x7ba2  ld s7,40(sp) *)
  Lemma wri_e2 : kernel_text -∗ instr (mword_of_int (WR + 0xe2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (WR + 0xe2)%Z (mword_of_int 0x7ba2 : mword 16)
    (mword_of_int (WR + 0xe2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) wrdc_7ba2 exec_execute_C_LDSP. Qed.

  (* 0x6165  addi sp,sp,112 *)
  Lemma wri_e4 : kernel_text -∗ instr (mword_of_int (WR + 0xe4) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 7 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (WR + 0xe4)%Z (mword_of_int 0x6165 : mword 16)
    (mword_of_int (WR + 0xe4) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 7 : mword 6), sp, sp, ADDI)) wrdc_6165 exec_execute_C_ADDI16SP. Qed.

  (* 0x8082  ret *)
  Lemma wri_e6 : kernel_text -∗ instr (mword_of_int (WR + 0xe6) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (WR + 0xe6)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (WR + 0xe6) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* 0x89da  mv s3,s6 *)
  Lemma wri_e8 : kernel_text -∗ instr (mword_of_int (WR + 0xe8) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (WR + 0xe8)%Z (mword_of_int 0x89da : mword 16)
    (mword_of_int (WR + 0xe8) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 19), ADD)) wrdc_89da exec_execute_C_MV. Qed.

  (* 0xb7cd  j 8000371e [+0xcc] *)
  Lemma wri_ea : kernel_text -∗ instr (mword_of_int (WR + 0xea) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WR + 0xea)%Z (mword_of_int 0xb7cd : mword 16)
    (mword_of_int (WR + 0xea) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)) cdec_b7cd exec_execute_C_J. Qed.

  (* 0x64e6  ld s1,88(sp) *)
  Lemma wri_ec : kernel_text -∗ instr (mword_of_int (WR + 0xec) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (WR + 0xec)%Z (mword_of_int 0x64e6 : mword 16)
    (mword_of_int (WR + 0xec) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) wrdc_64e6 exec_execute_C_LDSP. Qed.

  (* 0x7c02  ld s8,32(sp) *)
  Lemma wri_ee : kernel_text -∗ instr (mword_of_int (WR + 0xee) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (WR + 0xee)%Z (mword_of_int 0x7c02 : mword 16)
    (mword_of_int (WR + 0xee) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) wrdc_7c02 exec_execute_C_LDSP. Qed.

  (* 0x6ce2  ld s9,24(sp) *)
  Lemma wri_f0 : kernel_text -∗ instr (mword_of_int (WR + 0xf0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).
  Proof. mk_rvc (WR + 0xf0)%Z (mword_of_int 0x6ce2 : mword 16)
    (mword_of_int (WR + 0xf0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) wrdc_6ce2 exec_execute_C_LDSP. Qed.

  (* 0x6d42  ld s10,16(sp) *)
  Lemma wri_f2 : kernel_text -∗ instr (mword_of_int (WR + 0xf2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).
  Proof. mk_rvc (WR + 0xf2)%Z (mword_of_int 0x6d42 : mword 16)
    (mword_of_int (WR + 0xf2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) wrdc_6d42 exec_execute_C_LDSP. Qed.

  (* 0x6da2  ld s11,8(sp) *)
  Lemma wri_f4 : kernel_text -∗ instr (mword_of_int (WR + 0xf4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)).
  Proof. mk_rvc (WR + 0xf4)%Z (mword_of_int 0x6da2 : mword 16)
    (mword_of_int (WR + 0xf4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 27), false, 8)) wrdc_6da2 exec_execute_C_LDSP. Qed.

  (* 0xbfd9  j 8000371e [+0xcc] *)
  Lemma wri_f6 : kernel_text -∗ instr (mword_of_int (WR + 0xf6) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WR + 0xf6)%Z (mword_of_int 0xbfd9 : mword 16)
    (mword_of_int (WR + 0xf6) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)) cdec_bfd9 exec_execute_C_J. Qed.

  (* 0x557d  li a0,-1 *)
  Lemma wri_f8 : kernel_text -∗ instr (mword_of_int (WR + 0xf8) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (WR + 0xf8)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (WR + 0xf8) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  (* 0x8082  ret *)
  Lemma wri_fa : kernel_text -∗ instr (mword_of_int (WR + 0xfa) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (WR + 0xfa)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (WR + 0xfa) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* 0x557d  li a0,-1 *)
  Lemma wri_fc : kernel_text -∗ instr (mword_of_int (WR + 0xfc) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (WR + 0xfc)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (WR + 0xfc) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  (* 0xbfe1  j 80003728 [+0xd6] *)
  Lemma wri_fe : kernel_text -∗ instr (mword_of_int (WR + 0xfe) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (WR + 0xfe)%Z (mword_of_int 0xbfe1 : mword 16)
    (mword_of_int (WR + 0xfe) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)) cdec_bfe1 exec_execute_C_J. Qed.

End WriteiInstrs.

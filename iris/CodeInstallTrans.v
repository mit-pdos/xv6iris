(* CodeInstallTrans.v -- the instruction-DECODE layer for xv6's install_trans().
   For EVERY instruction of

     install_trans @ 0x80003a8c .. 0x80003b56  (offsets 0x00 .. 0xca, 204 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([iti_<off>]) plus
   the per-instruction decode facts they consume ([itdc_<word>] compressed /
   [itdb_<word>] base / [itcx_<word>] the compressed leaf expansions).
   install_trans is [static], called from initlog (recover_from_log, with
   recovering = 1) and from end_op (commit, with recovering = 0).

   STRUCT LOG.  [struct log log] lives at 0x80022318 (KernelSyms/log.c).  The
   field offsets below are READ OFF the lw/sw displacements in this image, not
   from the C declaration order, and they are the SAME in every one of the six
   log.c functions:

     +0x00 (0)   struct spinlock lock   -- 24 bytes: locked@+0, name@+8, cpu@+16
     +0x18 (24)  int start              -- first on-disk log block  (0x80022330)
     +0x1c (28)  int outstanding        --                          (0x80022334)
     +0x20 (32)  int committing         --                          (0x80022338)
     +0x24 (36)  int dev                --                          (0x8002233c)
     +0x28 (40)  int ncommit            --                          (0x80022340)
     +0x2c (44)  int lh.n               --                          (0x80022344)
     +0x30 (48)  int lh.block[LOGBLOCKS]--                          (0x80022348)

   Evidence in the image: the disassembler's own symbolisation of the three
   auipc/addi pairs -- [80022318 <log>], [80022344 <log+0x2c>] (lh.n),
   [80022334 <log+0x1c>] (outstanding), [80022348 <log+0x30>] (lh.block) --
   plus [lw a1,24] / [sw a1,24] against sb->logstart (start), [lw a5,32]
   guarding the sleeps (committing), [lw a0,36] feeding bread's dev argument
   (dev), and [lw a5,40; addiw a5,a5,1; sw a5,40] in end_op (ncommit).  There
   is NO [size] field in this xv6's [struct log].  LOGBLOCKS = 30, so
   sizeof(logheader) = 4 + 4*30 = 124 and sizeof(log) = 48 + 124 = 172.
   A [struct buf]'s payload [data] begins at +88 and [blockno] at +12.

   Byte-exact disassembly (from the tracked kernel-rocq/KernelInstrs.v, NOT
   xv6-riscv/kernel/kernel.asm, which has drifted):

     0x00 0001f797 auipc a5,0x1f
     0x04 8b87a783 lw a5,-1864(a5) # 80022344 <log+0x2c>
     0x08 0cf05163 blez a5,80003b56 <install_trans+0xca>
     0x0c 715d     addi sp,sp,-80
     0x0e e486     sd ra,72(sp)
     0x10 e0a2     sd s0,64(sp)
     0x12 fc26     sd s1,56(sp)
     0x14 f84a     sd s2,48(sp)
     0x16 f44e     sd s3,40(sp)
     0x18 f052     sd s4,32(sp)
     0x1a ec56     sd s5,24(sp)
     0x1c e85a     sd s6,16(sp)
     0x1e e45e     sd s7,8(sp)
     0x20 e062     sd s8,0(sp)
     0x22 0880     addi s0,sp,80
     0x24 8b2a     mv s6,a0
     0x26 0001fa97 auipc s5,0x1f
     0x2a 896a8a93 addi s5,s5,-1898 # 80022348 <log+0x30>
     0x2e 4981     li s3,0
     0x30 00004c17 auipc s8,0x4
     0x34 a1cc0c13 addi s8,s8,-1508 # 800074d8 <etext+0x4d8>
     0x38 0001fa17 auipc s4,0x1f
     0x3c 854a0a13 addi s4,s4,-1964 # 80022318 <log>
     0x40 40000b93 li s7,1024
     0x44 a025     j 80003af8 <install_trans+0x6c>
     0x46 000aa603 lw a2,0(s5)
     0x4a 85ce     mv a1,s3
     0x4c 8562     mv a0,s8
     0x4e a23fc0ef jal 800004fc <printk>
     0x52 a839     j 80003afc <install_trans+0x70>
     0x54 854a     mv a0,s2
     0x56 95cff0ef jal 80002c3e <brelse>
     0x5a 8526     mv a0,s1
     0x5c 956ff0ef jal 80002c3e <brelse>
     0x60 2985     addiw s3,s3,1
     0x62 0a91     addi s5,s5,4
     0x64 02ca2783 lw a5,44(s4)
     0x68 04f9d563 bge s3,a5,80003b3e <install_trans+0xb2>
     0x6c fc0b1de3 bnez s6,80003ad2 <install_trans+0x46>
     0x70 018a2583 lw a1,24(s4)
     0x74 013585bb addw a1,a1,s3
     0x78 2585     addiw a1,a1,1
     0x7a 024a2503 lw a0,36(s4)
     0x7e 82cff0ef jal 80002b36 <bread>
     0x82 892a     mv s2,a0
     0x84 000aa583 lw a1,0(s5)
     0x88 024a2503 lw a0,36(s4)
     0x8c 81eff0ef jal 80002b36 <bread>
     0x90 84aa     mv s1,a0
     0x92 865e     mv a2,s7
     0x94 05890593 addi a1,s2,88
     0x98 05850513 addi a0,a0,88
     0x9c a00fd0ef jal 80000d28 <memmove>
     0xa0 8526     mv a0,s1
     0xa2 8deff0ef jal 80002c0c <bwrite>
     0xa6 fa0b17e3 bnez s6,80003ae0 <install_trans+0x54>
     0xaa 8526     mv a0,s1
     0xac 9beff0ef jal 80002cf6 <bunpin>
     0xb0 b755     j 80003ae0 <install_trans+0x54>
     0xb2 60a6     ld ra,72(sp)
     0xb4 6406     ld s0,64(sp)
     0xb6 74e2     ld s1,56(sp)
     0xb8 7942     ld s2,48(sp)
     0xba 79a2     ld s3,40(sp)
     0xbc 7a02     ld s4,32(sp)
     0xbe 6ae2     ld s5,24(sp)
     0xc0 6b42     ld s6,16(sp)
     0xc2 6ba2     ld s7,8(sp)
     0xc4 6c02     ld s8,0(sp)
     0xc6 6161     addi sp,sp,80
     0xc8 8082     ret
     0xca 8082     ret

   STRUCTURE.
     PRE-FRAME TEST.  The function tests log.lh.n BEFORE it builds a frame:
       +0x00/+0x04  auipc a5,0x1f ; lw a5,-1864(a5)   a5 = log.lh.n (0x80022344)
       +0x08        blez a5 -> +0xca                  n <= 0: [c.ret] at +0xca
                                                      with NO prologue at all.
     So there are TWO return sites: +0xc8 (the epilogue's ret) and +0xca (the
     bare early ret), and the frame only exists on the +0x0c..+0xc8 path.
     Frame: 80 bytes ([c.addi sp,sp,-80] at +0x0c, [c.addi16sp sp,80] at +0xc6).
       Saved: ra@72, s0@64, s1@56, s2@48, s3@40, s4@32, s5@24, s6@16, s7@8,
       s8@0; s0 = sp+80.  All ten are restored at +0xb2..+0xc4.
     Register roles: s6 = the [recovering] argument (from a0 at +0x24);
       s5 = &log.lh.block[tail], the walking cursor; s4 = &log (0x80022318);
       s3 = tail, the induction variable; s8 = 0x800074d8, the printk format
       string "recovering tail %d dst %d\n"; s7 = 1024 = BSIZE, memmove's
       count; s2 = lbuf (the log block); s1 = dbuf (the destination block).
     Log fields touched: READS log.lh.n(+44) @+0x04 and @+0x64,
       log.start(+24) @+0x70, log.dev(+36) @+0x7a and @+0x88,
       log.lh.block[tail](+48+4*tail) @+0x46 and @+0x84.  WRITES none.
     Call sites (all four-byte [jal ra]):
       +0x4e  jal printk   (0x800004fc)  a0 = s8 (fmt), a1 = s3 (tail),
                                         a2 = log.lh.block[tail]
       +0x7e  jal bread    (0x80002b36)  a0 = log.dev, a1 = log.start+tail+1
                                         -> lbuf, parked in s2 at +0x82
       +0x8c  jal bread    (0x80002b36)  a0 = log.dev, a1 = log.lh.block[tail]
                                         -> dbuf, parked in s1 at +0x90
       +0x9c  jal memmove  (0x80000d28)  a0 = dbuf+88, a1 = lbuf+88, a2 = 1024
       +0xa2  jal bwrite   (0x80002c0c)  a0 = s1 (dbuf)
       +0xac  jal bunpin   (0x80002cf6)  a0 = s1 (dbuf)   [recovering == 0 only]
       +0x56  jal brelse   (0x80002c3e)  a0 = s2 (lbuf)
       +0x5c  jal brelse   (0x80002c3e)  a0 = s1 (dbuf)
     Loop (the [for (tail = 0; tail < log.lh.n; tail++)] body):
       entry   +0x44  j -> +0x6c   (jumps straight to the recovering TEST, so
                                    the first iteration starts at +0x6c)
       test    +0x6c  bnez s6 -> +0x46   (recovering: run the printk block,
                                          which falls back in via [j +0x70])
       body    +0x70 .. +0xa2, then the recovering-dependent bunpin split, then
               the two brelse calls at +0x54..+0x5e
       bump    +0x60  addiw s3,s3,1 ; +0x62  addi s5,s5,4
       back    +0x68  bge s3,a5 -> +0xb2 NOT taken (a5 = log.lh.n reloaded at
               +0x64); the back edge is the FALL-THROUGH into +0x6c
       exit    +0x68  taken -> +0xb2 (the epilogue)
       induction variable: s3 (tail), with s5 = &log.lh.block[tail] in lock step.
     Branch structure (five conditional/unconditional transfers in all):
       +0x08  blez a5   -> +0xca   (empty log: bare return)
       +0x44  j         -> +0x6c   (loop entry)
       +0x52  j         -> +0x70   (end of the printk block)
       +0x68  bge s3,a5 -> +0xb2   (loop exit)
       +0x6c  bnez s6   -> +0x46   (recovering: printk)
       +0xa6  bnez s6   -> +0x54   (recovering: skip bunpin)
       +0xb0  j         -> +0x54   (after bunpin, join the brelse pair)
     No panic site.  Every instruction is reachable (both values of recovering
     occur: initlog passes 1, end_op passes 0).

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (30 words):
         0x715d, 0xe486, 0xe0a2, 0xfc26, 0xf84a, 0xf44e, 0xf052, 0xec56,
         0xe85a, 0xe45e, 0xe062, 0x0880, 0x4981, 0xa025, 0x85ce, 0x854a,
         0x8526, 0x892a, 0x84aa, 0x60a6, 0x6406, 0x74e2, 0x7942, 0x79a2,
         0x7a02, 0x6ae2, 0x6b42, 0x6ba2, 0x6161, 0x8082

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0x8b2a -- also CodeUvmcopy.v:ucdc_8b2a
     0x2985 -- also CodePiperead.v:prdc_2985
     0x81eff0ef -- also CodeSysPipe.v:spdb_81eff0ef
     0x865e -- also CodeUvmalloc.v:uadc_865e
     0xb755 -- also CodeCopyout.v:codc_b755
     0x6c02 -- also CodeProcMapstacks.v:pmsdec_92
   Also duplicated WITHIN the six new log.c decode files (same argument --
   these are the strongest promotion candidates):
     0x0a91 (+ end_op), 0x02ca2783 (+ end_op), 0x018a2583 (+ end_op),
     0x2585 (+ end_op), 0x024a2503 (+ end_op), 0x000aa583 (+ end_op)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts private to install_trans.                    *)
(* ===================================================================== *)

(* 0x8b2a  mv s6,a0 *)
Lemma itdc_8b2a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b2a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 22), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8562  mv a0,s8 *)
Lemma itdc_8562 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8562 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa839  j 80003afc <install_trans+0x70> *)
Lemma itdc_a839 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa839 : mword 16)) s
  = Some (C_J (mword_of_int 15), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2985  addiw s3,s3,1 *)
Lemma itdc_2985 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2985 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0a91  addi s5,s5,4 *)
Lemma itdc_0a91 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0a91 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2585  addiw a1,a1,1 *)
Lemma itdc_2585 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2585 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x865e  mv a2,s7 *)
Lemma itdc_865e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x865e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb755  j 80003ae0 <install_trans+0x54> *)
Lemma itdc_b755 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb755 : mword 16)) s
  = Some (C_J (mword_of_int 2002), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6c02  ld s8,0(sp) *)
Lemma itdc_6c02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6c02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to install_trans.                  *)
(* ===================================================================== *)

(* 0x0001f797  auipc a5,0x1f *)
Lemma itdb_0001f797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001f797 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x8b87a783  lw a5,-1864(a5) # 80022344 <log+0x2c> *)
Lemma itdb_8b87a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8b87a783 : mword 32)) s
  = Some (LOAD (mword_of_int 2232 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x0cf05163  blez a5,80003b56 <install_trans+0xca> *)
Lemma itdb_0cf05163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0cf05163 : mword 32)) s
  = Some (BTYPE (mword_of_int 194 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001fa97  auipc s5,0x1f *)
Lemma itdb_0001fa97 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001fa97 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 21), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x896a8a93  addi s5,s5,-1898 # 80022348 <log+0x30> *)
Lemma itdb_896a8a93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x896a8a93 : mword 32)) s
  = Some (ITYPE (mword_of_int 2198 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x00004c17  auipc s8,0x4 *)
Lemma itdb_00004c17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004c17 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 24), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0xa1cc0c13  addi s8,s8,-1508 # 800074d8 <etext+0x4d8> *)
Lemma itdb_a1cc0c13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa1cc0c13 : mword 32)) s
  = Some (ITYPE (mword_of_int 2588 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 24), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001fa17  auipc s4,0x1f *)
Lemma itdb_0001fa17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001fa17 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x854a0a13  addi s4,s4,-1964 # 80022318 <log> *)
Lemma itdb_854a0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x854a0a13 : mword 32)) s
  = Some (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x40000b93  li s7,1024 *)
Lemma itdb_40000b93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40000b93 : mword 32)) s
  = Some (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 23), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x000aa603  lw a2,0(s5) *)
Lemma itdb_000aa603 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000aa603 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 12), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xa23fc0ef  jal 800004fc <printk> *)
Lemma itdb_a23fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa23fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083362 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x95cff0ef  jal 80002c3e <brelse> *)
Lemma itdb_95cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x95cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093404 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x956ff0ef  jal 80002c3e <brelse> *)
Lemma itdb_956ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x956ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093398 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x02ca2783  lw a5,44(s4) *)
Lemma itdb_02ca2783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02ca2783 : mword 32)) s
  = Some (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x04f9d563  bge s3,a5,80003b3e <install_trans+0xb2> *)
Lemma itdb_04f9d563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04f9d563 : mword 32)) s
  = Some (BTYPE (mword_of_int 74 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 19), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0xfc0b1de3  bnez s6,80003ad2 <install_trans+0x46> *)
Lemma itdb_fc0b1de3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc0b1de3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0x018a2583  lw a1,24(s4) *)
Lemma itdb_018a2583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x018a2583 : mword 32)) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x013585bb  addw a1,a1,s3 *)
Lemma itdb_013585bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x013585bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW), s).
Proof. decode_bridge_ms. Qed.

(* 0x024a2503  lw a0,36(s4) *)
Lemma itdb_024a2503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x024a2503 : mword 32)) s
  = Some (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x82cff0ef  jal 80002b36 <bread> *)
Lemma itdb_82cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x82cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093100 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x000aa583  lw a1,0(s5) *)
Lemma itdb_000aa583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000aa583 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x81eff0ef  jal 80002b36 <bread> *)
Lemma itdb_81eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x05890593  addi a1,s2,88 *)
Lemma itdb_05890593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05890593 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x05850513  addi a0,a0,88 *)
Lemma itdb_05850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xa00fd0ef  jal 80000d28 <memmove> *)
Lemma itdb_a00fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa00fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2085376 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x8deff0ef  jal 80002c0c <bwrite> *)
Lemma itdb_8deff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8deff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093278 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfa0b17e3  bnez s6,80003ae0 <install_trans+0x54> *)
Lemma itdb_fa0b17e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa0b17e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8110 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0x9beff0ef  jal 80002cf6 <bunpin> *)
Lemma itdb_9beff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9beff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093502 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InstallTransInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation IT := KernelSyms.install_trans.

  (* 0x00  0001f797  auipc a5,0x1f *)
  Lemma iti_00 : kernel_text -∗ instr (mword_of_int (IT + 0x00) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (IT + 0x00)%Z (mword_of_int 0x0001f797 : mword 32)
    (mword_of_int (IT + 0x00) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 15), AUIPC)) itdb_0001f797. Qed.

  (* 0x04  8b87a783  lw a5,-1864(a5) # 80022344 <log+0x2c> *)
  Lemma iti_04 : kernel_text -∗ instr (mword_of_int (IT + 0x04) : mword 64) false (LOAD (mword_of_int 2232 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (IT + 0x04)%Z (mword_of_int 0x8b87a783 : mword 32)
    (mword_of_int (IT + 0x04) : mword 64) (LOAD (mword_of_int 2232 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) itdb_8b87a783. Qed.

  (* 0x08  0cf05163  blez a5,80003b56 <install_trans+0xca> *)
  Lemma iti_08 : kernel_text -∗ instr (mword_of_int (IT + 0x08) : mword 64) false (BTYPE (mword_of_int 194 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (IT + 0x08)%Z (mword_of_int 0x0cf05163 : mword 32)
    (mword_of_int (IT + 0x08) : mword 64) (BTYPE (mword_of_int 194 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) itdb_0cf05163. Qed.

  (* 0x0c  715d  addi sp,sp,-80 *)
  Lemma iti_0c : kernel_text -∗ instr (mword_of_int (IT + 0x0c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (IT + 0x0c)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (IT + 0x0c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  (* 0x0e  e486  sd ra,72(sp) *)
  Lemma iti_0e : kernel_text -∗ instr (mword_of_int (IT + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (IT + 0x0e)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (IT + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  (* 0x10  e0a2  sd s0,64(sp) *)
  Lemma iti_10 : kernel_text -∗ instr (mword_of_int (IT + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (IT + 0x10)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (IT + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  (* 0x12  fc26  sd s1,56(sp) *)
  Lemma iti_12 : kernel_text -∗ instr (mword_of_int (IT + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (IT + 0x12)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (IT + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  (* 0x14  f84a  sd s2,48(sp) *)
  Lemma iti_14 : kernel_text -∗ instr (mword_of_int (IT + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (IT + 0x14)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (IT + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  (* 0x16  f44e  sd s3,40(sp) *)
  Lemma iti_16 : kernel_text -∗ instr (mword_of_int (IT + 0x16) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (IT + 0x16)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (IT + 0x16) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  (* 0x18  f052  sd s4,32(sp) *)
  Lemma iti_18 : kernel_text -∗ instr (mword_of_int (IT + 0x18) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (IT + 0x18)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (IT + 0x18) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  (* 0x1a  ec56  sd s5,24(sp) *)
  Lemma iti_1a : kernel_text -∗ instr (mword_of_int (IT + 0x1a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (IT + 0x1a)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (IT + 0x1a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  (* 0x1c  e85a  sd s6,16(sp) *)
  Lemma iti_1c : kernel_text -∗ instr (mword_of_int (IT + 0x1c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (IT + 0x1c)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (IT + 0x1c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  (* 0x1e  e45e  sd s7,8(sp) *)
  Lemma iti_1e : kernel_text -∗ instr (mword_of_int (IT + 0x1e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (IT + 0x1e)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (IT + 0x1e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  (* 0x20  e062  sd s8,0(sp) *)
  Lemma iti_20 : kernel_text -∗ instr (mword_of_int (IT + 0x20) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (IT + 0x20)%Z (mword_of_int 0xe062 : mword 16)
    (mword_of_int (IT + 0x20) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e062 exec_execute_C_SDSP. Qed.

  (* 0x22  0880  addi s0,sp,80 *)
  Lemma iti_22 : kernel_text -∗ instr (mword_of_int (IT + 0x22) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (IT + 0x22)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (IT + 0x22) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  (* 0x24  8b2a  mv s6,a0 *)
  Lemma iti_24 : kernel_text -∗ instr (mword_of_int (IT + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (IT + 0x24)%Z (mword_of_int 0x8b2a : mword 16)
    (mword_of_int (IT + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 22), ADD)) itdc_8b2a exec_execute_C_MV. Qed.

  (* 0x26  0001fa97  auipc s5,0x1f *)
  Lemma iti_26 : kernel_text -∗ instr (mword_of_int (IT + 0x26) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 21), AUIPC)).
  Proof. mk_base (IT + 0x26)%Z (mword_of_int 0x0001fa97 : mword 32)
    (mword_of_int (IT + 0x26) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 21), AUIPC)) itdb_0001fa97. Qed.

  (* 0x2a  896a8a93  addi s5,s5,-1898 # 80022348 <log+0x30> *)
  Lemma iti_2a : kernel_text -∗ instr (mword_of_int (IT + 0x2a) : mword 64) false (ITYPE (mword_of_int 2198 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).
  Proof. mk_base (IT + 0x2a)%Z (mword_of_int 0x896a8a93 : mword 32)
    (mword_of_int (IT + 0x2a) : mword 64) (ITYPE (mword_of_int 2198 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) itdb_896a8a93. Qed.

  (* 0x2e  4981  li s3,0 *)
  Lemma iti_2e : kernel_text -∗ instr (mword_of_int (IT + 0x2e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (IT + 0x2e)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (IT + 0x2e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  (* 0x30  00004c17  auipc s8,0x4 *)
  Lemma iti_30 : kernel_text -∗ instr (mword_of_int (IT + 0x30) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 24), AUIPC)).
  Proof. mk_base (IT + 0x30)%Z (mword_of_int 0x00004c17 : mword 32)
    (mword_of_int (IT + 0x30) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 24), AUIPC)) itdb_00004c17. Qed.

  (* 0x34  a1cc0c13  addi s8,s8,-1508 # 800074d8 <etext+0x4d8> *)
  Lemma iti_34 : kernel_text -∗ instr (mword_of_int (IT + 0x34) : mword 64) false (ITYPE (mword_of_int 2588 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 24), ADDI)).
  Proof. mk_base (IT + 0x34)%Z (mword_of_int 0xa1cc0c13 : mword 32)
    (mword_of_int (IT + 0x34) : mword 64) (ITYPE (mword_of_int 2588 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 24), ADDI)) itdb_a1cc0c13. Qed.

  (* 0x38  0001fa17  auipc s4,0x1f *)
  Lemma iti_38 : kernel_text -∗ instr (mword_of_int (IT + 0x38) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (IT + 0x38)%Z (mword_of_int 0x0001fa17 : mword 32)
    (mword_of_int (IT + 0x38) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 20), AUIPC)) itdb_0001fa17. Qed.

  (* 0x3c  854a0a13  addi s4,s4,-1964 # 80022318 <log> *)
  Lemma iti_3c : kernel_text -∗ instr (mword_of_int (IT + 0x3c) : mword 64) false (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (IT + 0x3c)%Z (mword_of_int 0x854a0a13 : mword 32)
    (mword_of_int (IT + 0x3c) : mword 64) (ITYPE (mword_of_int 2132 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) itdb_854a0a13. Qed.

  (* 0x40  40000b93  li s7,1024 *)
  Lemma iti_40 : kernel_text -∗ instr (mword_of_int (IT + 0x40) : mword 64) false (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 23), ADDI)).
  Proof. mk_base (IT + 0x40)%Z (mword_of_int 0x40000b93 : mword 32)
    (mword_of_int (IT + 0x40) : mword 64) (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 23), ADDI)) itdb_40000b93. Qed.

  (* 0x44  a025  j 80003af8 <install_trans+0x6c> *)
  Lemma iti_44 : kernel_text -∗ instr (mword_of_int (IT + 0x44) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (IT + 0x44)%Z (mword_of_int 0xa025 : mword 16)
    (mword_of_int (IT + 0x44) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 20 : mword 11) ('b"0")), zreg)) cdec_a025 exec_execute_C_J. Qed.

  (* 0x46  000aa603  lw a2,0(s5) *)
  Lemma iti_46 : kernel_text -∗ instr (mword_of_int (IT + 0x46) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 12), false, 4)).
  Proof. mk_base (IT + 0x46)%Z (mword_of_int 0x000aa603 : mword 32)
    (mword_of_int (IT + 0x46) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 12), false, 4)) itdb_000aa603. Qed.

  (* 0x4a  85ce  mv a1,s3 *)
  Lemma iti_4a : kernel_text -∗ instr (mword_of_int (IT + 0x4a) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (IT + 0x4a)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (IT + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ce exec_execute_C_MV. Qed.

  (* 0x4c  8562  mv a0,s8 *)
  Lemma iti_4c : kernel_text -∗ instr (mword_of_int (IT + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IT + 0x4c)%Z (mword_of_int 0x8562 : mword 16)
    (mword_of_int (IT + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 10), ADD)) itdc_8562 exec_execute_C_MV. Qed.

  (* 0x4e  a23fc0ef  jal 800004fc <printk> *)
  Lemma iti_4e : kernel_text -∗ instr (mword_of_int (IT + 0x4e) : mword 64) false (JAL (mword_of_int 2083362 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x4e)%Z (mword_of_int 0xa23fc0ef : mword 32)
    (mword_of_int (IT + 0x4e) : mword 64) (JAL (mword_of_int 2083362 : mword 21, Regidx (mword_of_int 1))) itdb_a23fc0ef. Qed.

  (* 0x52  a839  j 80003afc <install_trans+0x70> *)
  Lemma iti_52 : kernel_text -∗ instr (mword_of_int (IT + 0x52) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 15 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (IT + 0x52)%Z (mword_of_int 0xa839 : mword 16)
    (mword_of_int (IT + 0x52) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 15 : mword 11) ('b"0")), zreg)) itdc_a839 exec_execute_C_J. Qed.

  (* 0x54  854a  mv a0,s2 *)
  Lemma iti_54 : kernel_text -∗ instr (mword_of_int (IT + 0x54) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IT + 0x54)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (IT + 0x54) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* 0x56  95cff0ef  jal 80002c3e <brelse> *)
  Lemma iti_56 : kernel_text -∗ instr (mword_of_int (IT + 0x56) : mword 64) false (JAL (mword_of_int 2093404 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x56)%Z (mword_of_int 0x95cff0ef : mword 32)
    (mword_of_int (IT + 0x56) : mword 64) (JAL (mword_of_int 2093404 : mword 21, Regidx (mword_of_int 1))) itdb_95cff0ef. Qed.

  (* 0x5a  8526  mv a0,s1 *)
  Lemma iti_5a : kernel_text -∗ instr (mword_of_int (IT + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IT + 0x5a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (IT + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x5c  956ff0ef  jal 80002c3e <brelse> *)
  Lemma iti_5c : kernel_text -∗ instr (mword_of_int (IT + 0x5c) : mword 64) false (JAL (mword_of_int 2093398 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x5c)%Z (mword_of_int 0x956ff0ef : mword 32)
    (mword_of_int (IT + 0x5c) : mword 64) (JAL (mword_of_int 2093398 : mword 21, Regidx (mword_of_int 1))) itdb_956ff0ef. Qed.

  (* 0x60  2985  addiw s3,s3,1 *)
  Lemma iti_60 : kernel_text -∗ instr (mword_of_int (IT + 0x60) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19))).
  Proof. mk_rvc (IT + 0x60)%Z (mword_of_int 0x2985 : mword 16)
    (mword_of_int (IT + 0x60) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19))) itdc_2985 exec_execute_C_ADDIW. Qed.

  (* 0x62  0a91  addi s5,s5,4 *)
  Lemma iti_62 : kernel_text -∗ instr (mword_of_int (IT + 0x62) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc (IT + 0x62)%Z (mword_of_int 0x0a91 : mword 16)
    (mword_of_int (IT + 0x62) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) itdc_0a91 exec_execute_C_ADDI. Qed.

  (* 0x64  02ca2783  lw a5,44(s4) *)
  Lemma iti_64 : kernel_text -∗ instr (mword_of_int (IT + 0x64) : mword 64) false (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (IT + 0x64)%Z (mword_of_int 0x02ca2783 : mword 32)
    (mword_of_int (IT + 0x64) : mword 64) (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4)) itdb_02ca2783. Qed.

  (* 0x68  04f9d563  bge s3,a5,80003b3e <install_trans+0xb2> *)
  Lemma iti_68 : kernel_text -∗ instr (mword_of_int (IT + 0x68) : mword 64) false (BTYPE (mword_of_int 74 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 19), BGE)).
  Proof. mk_base (IT + 0x68)%Z (mword_of_int 0x04f9d563 : mword 32)
    (mword_of_int (IT + 0x68) : mword 64) (BTYPE (mword_of_int 74 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 19), BGE)) itdb_04f9d563. Qed.

  (* 0x6c  fc0b1de3  bnez s6,80003ad2 <install_trans+0x46> *)
  Lemma iti_6c : kernel_text -∗ instr (mword_of_int (IT + 0x6c) : mword 64) false (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE)).
  Proof. mk_base (IT + 0x6c)%Z (mword_of_int 0xfc0b1de3 : mword 32)
    (mword_of_int (IT + 0x6c) : mword 64) (BTYPE (mword_of_int 8154 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE)) itdb_fc0b1de3. Qed.

  (* 0x70  018a2583  lw a1,24(s4) *)
  Lemma iti_70 : kernel_text -∗ instr (mword_of_int (IT + 0x70) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (IT + 0x70)%Z (mword_of_int 0x018a2583 : mword 32)
    (mword_of_int (IT + 0x70) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4)) itdb_018a2583. Qed.

  (* 0x74  013585bb  addw a1,a1,s3 *)
  Lemma iti_74 : kernel_text -∗ instr (mword_of_int (IT + 0x74) : mword 64) false (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW)).
  Proof. mk_base (IT + 0x74)%Z (mword_of_int 0x013585bb : mword 32)
    (mword_of_int (IT + 0x74) : mword 64) (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW)) itdb_013585bb. Qed.

  (* 0x78  2585  addiw a1,a1,1 *)
  Lemma iti_78 : kernel_text -∗ instr (mword_of_int (IT + 0x78) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11))).
  Proof. mk_rvc (IT + 0x78)%Z (mword_of_int 0x2585 : mword 16)
    (mword_of_int (IT + 0x78) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11))) itdc_2585 exec_execute_C_ADDIW. Qed.

  (* 0x7a  024a2503  lw a0,36(s4) *)
  Lemma iti_7a : kernel_text -∗ instr (mword_of_int (IT + 0x7a) : mword 64) false (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (IT + 0x7a)%Z (mword_of_int 0x024a2503 : mword 32)
    (mword_of_int (IT + 0x7a) : mword 64) (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)) itdb_024a2503. Qed.

  (* 0x7e  82cff0ef  jal 80002b36 <bread> *)
  Lemma iti_7e : kernel_text -∗ instr (mword_of_int (IT + 0x7e) : mword 64) false (JAL (mword_of_int 2093100 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x7e)%Z (mword_of_int 0x82cff0ef : mword 32)
    (mword_of_int (IT + 0x7e) : mword 64) (JAL (mword_of_int 2093100 : mword 21, Regidx (mword_of_int 1))) itdb_82cff0ef. Qed.

  (* 0x82  892a  mv s2,a0 *)
  Lemma iti_82 : kernel_text -∗ instr (mword_of_int (IT + 0x82) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (IT + 0x82)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (IT + 0x82) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  (* 0x84  000aa583  lw a1,0(s5) *)
  Lemma iti_84 : kernel_text -∗ instr (mword_of_int (IT + 0x84) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (IT + 0x84)%Z (mword_of_int 0x000aa583 : mword 32)
    (mword_of_int (IT + 0x84) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4)) itdb_000aa583. Qed.

  (* 0x88  024a2503  lw a0,36(s4) *)
  Lemma iti_88 : kernel_text -∗ instr (mword_of_int (IT + 0x88) : mword 64) false (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (IT + 0x88)%Z (mword_of_int 0x024a2503 : mword 32)
    (mword_of_int (IT + 0x88) : mword 64) (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)) itdb_024a2503. Qed.

  (* 0x8c  81eff0ef  jal 80002b36 <bread> *)
  Lemma iti_8c : kernel_text -∗ instr (mword_of_int (IT + 0x8c) : mword 64) false (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x8c)%Z (mword_of_int 0x81eff0ef : mword 32)
    (mword_of_int (IT + 0x8c) : mword 64) (JAL (mword_of_int 2093086 : mword 21, Regidx (mword_of_int 1))) itdb_81eff0ef. Qed.

  (* 0x90  84aa  mv s1,a0 *)
  Lemma iti_90 : kernel_text -∗ instr (mword_of_int (IT + 0x90) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (IT + 0x90)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (IT + 0x90) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0x92  865e  mv a2,s7 *)
  Lemma iti_92 : kernel_text -∗ instr (mword_of_int (IT + 0x92) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (IT + 0x92)%Z (mword_of_int 0x865e : mword 16)
    (mword_of_int (IT + 0x92) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)) itdc_865e exec_execute_C_MV. Qed.

  (* 0x94  05890593  addi a1,s2,88 *)
  Lemma iti_94 : kernel_text -∗ instr (mword_of_int (IT + 0x94) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (IT + 0x94)%Z (mword_of_int 0x05890593 : mword 32)
    (mword_of_int (IT + 0x94) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), ADDI)) itdb_05890593. Qed.

  (* 0x98  05850513  addi a0,a0,88 *)
  Lemma iti_98 : kernel_text -∗ instr (mword_of_int (IT + 0x98) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (IT + 0x98)%Z (mword_of_int 0x05850513 : mword 32)
    (mword_of_int (IT + 0x98) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) itdb_05850513. Qed.

  (* 0x9c  a00fd0ef  jal 80000d28 <memmove> *)
  Lemma iti_9c : kernel_text -∗ instr (mword_of_int (IT + 0x9c) : mword 64) false (JAL (mword_of_int 2085376 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0x9c)%Z (mword_of_int 0xa00fd0ef : mword 32)
    (mword_of_int (IT + 0x9c) : mword 64) (JAL (mword_of_int 2085376 : mword 21, Regidx (mword_of_int 1))) itdb_a00fd0ef. Qed.

  (* 0xa0  8526  mv a0,s1 *)
  Lemma iti_a0 : kernel_text -∗ instr (mword_of_int (IT + 0xa0) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IT + 0xa0)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (IT + 0xa0) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0xa2  8deff0ef  jal 80002c0c <bwrite> *)
  Lemma iti_a2 : kernel_text -∗ instr (mword_of_int (IT + 0xa2) : mword 64) false (JAL (mword_of_int 2093278 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0xa2)%Z (mword_of_int 0x8deff0ef : mword 32)
    (mword_of_int (IT + 0xa2) : mword 64) (JAL (mword_of_int 2093278 : mword 21, Regidx (mword_of_int 1))) itdb_8deff0ef. Qed.

  (* 0xa6  fa0b17e3  bnez s6,80003ae0 <install_trans+0x54> *)
  Lemma iti_a6 : kernel_text -∗ instr (mword_of_int (IT + 0xa6) : mword 64) false (BTYPE (mword_of_int 8110 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE)).
  Proof. mk_base (IT + 0xa6)%Z (mword_of_int 0xfa0b17e3 : mword 32)
    (mword_of_int (IT + 0xa6) : mword 64) (BTYPE (mword_of_int 8110 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 22), BNE)) itdb_fa0b17e3. Qed.

  (* 0xaa  8526  mv a0,s1 *)
  Lemma iti_aa : kernel_text -∗ instr (mword_of_int (IT + 0xaa) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (IT + 0xaa)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (IT + 0xaa) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0xac  9beff0ef  jal 80002cf6 <bunpin> *)
  Lemma iti_ac : kernel_text -∗ instr (mword_of_int (IT + 0xac) : mword 64) false (JAL (mword_of_int 2093502 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IT + 0xac)%Z (mword_of_int 0x9beff0ef : mword 32)
    (mword_of_int (IT + 0xac) : mword 64) (JAL (mword_of_int 2093502 : mword 21, Regidx (mword_of_int 1))) itdb_9beff0ef. Qed.

  (* 0xb0  b755  j 80003ae0 <install_trans+0x54> *)
  Lemma iti_b0 : kernel_text -∗ instr (mword_of_int (IT + 0xb0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (IT + 0xb0)%Z (mword_of_int 0xb755 : mword 16)
    (mword_of_int (IT + 0xb0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")), zreg)) itdc_b755 exec_execute_C_J. Qed.

  (* 0xb2  60a6  ld ra,72(sp) *)
  Lemma iti_b2 : kernel_text -∗ instr (mword_of_int (IT + 0xb2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (IT + 0xb2)%Z (mword_of_int 0x60a6 : mword 16)
    (mword_of_int (IT + 0xb2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.

  (* 0xb4  6406  ld s0,64(sp) *)
  Lemma iti_b4 : kernel_text -∗ instr (mword_of_int (IT + 0xb4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (IT + 0xb4)%Z (mword_of_int 0x6406 : mword 16)
    (mword_of_int (IT + 0xb4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.

  (* 0xb6  74e2  ld s1,56(sp) *)
  Lemma iti_b6 : kernel_text -∗ instr (mword_of_int (IT + 0xb6) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (IT + 0xb6)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (IT + 0xb6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  (* 0xb8  7942  ld s2,48(sp) *)
  Lemma iti_b8 : kernel_text -∗ instr (mword_of_int (IT + 0xb8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (IT + 0xb8)%Z (mword_of_int 0x7942 : mword 16)
    (mword_of_int (IT + 0xb8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.

  (* 0xba  79a2  ld s3,40(sp) *)
  Lemma iti_ba : kernel_text -∗ instr (mword_of_int (IT + 0xba) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (IT + 0xba)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (IT + 0xba) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  (* 0xbc  7a02  ld s4,32(sp) *)
  Lemma iti_bc : kernel_text -∗ instr (mword_of_int (IT + 0xbc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (IT + 0xbc)%Z (mword_of_int 0x7a02 : mword 16)
    (mword_of_int (IT + 0xbc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.

  (* 0xbe  6ae2  ld s5,24(sp) *)
  Lemma iti_be : kernel_text -∗ instr (mword_of_int (IT + 0xbe) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (IT + 0xbe)%Z (mword_of_int 0x6ae2 : mword 16)
    (mword_of_int (IT + 0xbe) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.

  (* 0xc0  6b42  ld s6,16(sp) *)
  Lemma iti_c0 : kernel_text -∗ instr (mword_of_int (IT + 0xc0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (IT + 0xc0)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (IT + 0xc0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  (* 0xc2  6ba2  ld s7,8(sp) *)
  Lemma iti_c2 : kernel_text -∗ instr (mword_of_int (IT + 0xc2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (IT + 0xc2)%Z (mword_of_int 0x6ba2 : mword 16)
    (mword_of_int (IT + 0xc2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.

  (* 0xc4  6c02  ld s8,0(sp) *)
  Lemma iti_c4 : kernel_text -∗ instr (mword_of_int (IT + 0xc4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (IT + 0xc4)%Z (mword_of_int 0x6c02 : mword 16)
    (mword_of_int (IT + 0xc4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) itdc_6c02 exec_execute_C_LDSP. Qed.

  (* 0xc6  6161  addi sp,sp,80 *)
  Lemma iti_c6 : kernel_text -∗ instr (mword_of_int (IT + 0xc6) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (IT + 0xc6)%Z (mword_of_int 0x6161 : mword 16)
    (mword_of_int (IT + 0xc6) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.

  (* 0xc8  8082  ret *)
  Lemma iti_c8 : kernel_text -∗ instr (mword_of_int (IT + 0xc8) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IT + 0xc8)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (IT + 0xc8) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* 0xca  8082  ret *)
  Lemma iti_ca : kernel_text -∗ instr (mword_of_int (IT + 0xca) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IT + 0xca)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (IT + 0xca) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End InstallTransInstrs.

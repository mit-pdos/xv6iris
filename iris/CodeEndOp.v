(* CodeEndOp.v -- the instruction-DECODE layer for xv6's end_op().
   For EVERY instruction of

     end_op @ 0x80003c4a .. 0x80003d6a   (offsets 0x00 .. 0x120, 290 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([eoi_<off>]) plus
   the per-instruction decode facts they consume ([eodc_<word>] compressed /
   [eodb_<word>] base / [eocx_<word>] the compressed leaf expansions).
   Both [commit] and [write_log] are [static] with end_op their only caller, so
   gcc INLINED them: this one function contains the accounting critical
   section, the "log.committing" panic arm, the wakeup arm, the whole
   write_log copy loop, and the write_head / install_trans / write_head commit
   sequence.

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

     0x00 7139     addi sp,sp,-64
     0x02 fc06     sd ra,56(sp)
     0x04 f822     sd s0,48(sp)
     0x06 f426     sd s1,40(sp)
     0x08 f04a     sd s2,32(sp)
     0x0a 0080     addi s0,sp,64
     0x0c 0001e497 auipc s1,0x1e
     0x10 6c248493 addi s1,s1,1730 # 80022318 <log>
     0x14 8526     mv a0,s1
     0x16 fa9fc0ef jal 80000c08 <acquire>
     0x1a 4cdc     lw a5,28(s1)
     0x1c 37fd     addiw a5,a5,-1
     0x1e 893e     mv s2,a5
     0x20 ccdc     sw a5,28(s1)
     0x22 509c     lw a5,32(s1)
     0x24 e3b1     bnez a5,80003cb2 <end_op+0x68>
     0x26 04091a63 bnez s2,80003cc4 <end_op+0x7a>
     0x2a 0001e497 auipc s1,0x1e
     0x2e 6a448493 addi s1,s1,1700 # 80022318 <log>
     0x32 4785     li a5,1
     0x34 d09c     sw a5,32(s1)
     0x36 8526     mv a0,s1
     0x38 80efd0ef jal 80000c90 <release>
     0x3c 54dc     lw a5,44(s1)
     0x3e 06f04063 bgtz a5,80003ce8 <end_op+0x9e>
     0x42 0001e497 auipc s1,0x1e
     0x46 68c48493 addi s1,s1,1676 # 80022318 <log>
     0x4a 8526     mv a0,s1
     0x4c f73fc0ef jal 80000c08 <acquire>
     0x50 0204a023 sw zero,32(s1)
     0x54 549c     lw a5,40(s1)
     0x56 2785     addiw a5,a5,1
     0x58 d49c     sw a5,40(s1)
     0x5a 8526     mv a0,s1
     0x5c aacfe0ef jal 80001f52 <wakeup>
     0x60 8526     mv a0,s1
     0x62 fe5fc0ef jal 80000c90 <release>
     0x66 a035     j 80003cdc <end_op+0x92>
     0x68 ec4e     sd s3,24(sp)
     0x6a e852     sd s4,16(sp)
     0x6c e456     sd s5,8(sp)
     0x6e 00004517 auipc a0,0x4
     0x72 84850513 addi a0,a0,-1976 # 80007500 <etext+0x500>
     0x76 b67fc0ef jal 80000826 <panic>
     0x7a 0001e517 auipc a0,0x1e
     0x7e 65450513 addi a0,a0,1620 # 80022318 <log>
     0x82 a86fe0ef jal 80001f52 <wakeup>
     0x86 0001e517 auipc a0,0x1e
     0x8a 64850513 addi a0,a0,1608 # 80022318 <log>
     0x8e fb9fc0ef jal 80000c90 <release>
     0x92 70e2     ld ra,56(sp)
     0x94 7442     ld s0,48(sp)
     0x96 74a2     ld s1,40(sp)
     0x98 7902     ld s2,32(sp)
     0x9a 6121     addi sp,sp,64
     0x9c 8082     ret
     0x9e ec4e     sd s3,24(sp)
     0xa0 e852     sd s4,16(sp)
     0xa2 e456     sd s5,8(sp)
     0xa4 0001ea97 auipc s5,0x1e
     0xa8 65aa8a93 addi s5,s5,1626 # 80022348 <log+0x30>
     0xac 0001ea17 auipc s4,0x1e
     0xb0 622a0a13 addi s4,s4,1570 # 80022318 <log>
     0xb4 018a2583 lw a1,24(s4)
     0xb8 012585bb addw a1,a1,s2
     0xbc 2585     addiw a1,a1,1
     0xbe 024a2503 lw a0,36(s4)
     0xc2 e2bfe0ef jal 80002b36 <bread>
     0xc6 84aa     mv s1,a0
     0xc8 000aa583 lw a1,0(s5)
     0xcc 024a2503 lw a0,36(s4)
     0xd0 e1dfe0ef jal 80002b36 <bread>
     0xd4 89aa     mv s3,a0
     0xd6 40000613 li a2,1024
     0xda 05850593 addi a1,a0,88
     0xde 05848513 addi a0,s1,88
     0xe2 ffdfc0ef jal 80000d28 <memmove>
     0xe6 8526     mv a0,s1
     0xe8 edbfe0ef jal 80002c0c <bwrite>
     0xec 854e     mv a0,s3
     0xee f07fe0ef jal 80002c3e <brelse>
     0xf2 8526     mv a0,s1
     0xf4 f01fe0ef jal 80002c3e <brelse>
     0xf8 2905     addiw s2,s2,1
     0xfa 0a91     addi s5,s5,4
     0xfc 02ca2783 lw a5,44(s4)
     0x100 faf94ae3 blt s2,a5,80003cfe <end_op+0xb4>
     0x104 ce1ff0ef jal 80003a2e <write_head>
     0x108 4501     li a0,0
     0x10a d39ff0ef jal 80003a8c <install_trans>
     0x10e 0001e797 auipc a5,0x1e
     0x112 5e07a623 sw zero,1516(a5) # 80022344 <log+0x2c>
     0x116 ccfff0ef jal 80003a2e <write_head>
     0x11a 69e2     ld s3,24(sp)
     0x11c 6a42     ld s4,16(sp)
     0x11e 6aa2     ld s5,8(sp)
     0x120 b70d     j 80003c8c <end_op+0x42>

   STRUCTURE.
     Frame: 64 bytes ([c.addi16sp sp,-64] at +0x00, [c.addi16sp sp,64] at
       +0x9a).  Saved UNCONDITIONALLY: ra@56, s0@48, s1@40, s2@32; s0 = sp+64.
       Saved LAZILY, only on the two arms that clobber them:
         +0x68..+0x6c  sd s3,24(sp) ; sd s4,16(sp) ; sd s5,8(sp)  (panic arm)
         +0x9e..+0xa2  sd s3,24(sp) ; sd s4,16(sp) ; sd s5,8(sp)  (commit arm)
       and RESTORED only on the commit arm, at +0x11a..+0x11e.  The main
       epilogue at +0x92..+0x9c restores ra/s0/s1/s2 only -- so an end_op that
       never commits never touches s3/s4/s5 at all.
     Register roles: s1 = &log (0x80022318), re-materialised by its own
       auipc/addi pair at +0x0c, +0x2a and +0x42; s2 = the decremented
       log.outstanding (the C's [do_commit] decider) AND, on the commit arm,
       the write_log loop's [tail] induction variable (it is 0 exactly when the
       commit arm is taken, which is why gcc reuses it); s5 =
       &log.lh.block[tail]; s4 = &log; s3 = the "from" buffer inside the copy
       loop; a5 = assorted scratch.
     Log fields touched: READS log.outstanding(+28) @+0x1a,
       log.committing(+32) @+0x22, log.lh.n(+44) @+0x3c and @+0xfc,
       log.ncommit(+40) @+0x54, log.start(+24) @+0xb4, log.dev(+36) @+0xbe and
       @+0xcc, log.lh.block[tail](+48+4*tail) @+0xc8.
       WRITES log.outstanding(+28) @+0x20, log.committing(+32) @+0x34 (= 1) and
       @+0x50 (= 0), log.ncommit(+40) @+0x58 (+= 1), log.lh.n(+44) @+0x112
       (= 0, through the auipc/sw pair at +0x10e/+0x112 -> 0x80022344).
     Call sites (all four-byte [jal ra]):
       +0x16  jal acquire       (0x80000c08)  a0 = s1 = &log.lock
       +0x38  jal release       (0x80000c90)  a0 = s1
       +0x4c  jal acquire       (0x80000c08)  a0 = s1
       +0x5c  jal wakeup        (0x80001f52)  a0 = s1 (chan = &log)
       +0x62  jal release       (0x80000c90)  a0 = s1
       +0x76  jal panic         (0x80000826)  a0 = 0x80007500 "log.committing"
       +0x82  jal wakeup        (0x80001f52)  a0 = &log (own auipc/addi pair)
       +0x8e  jal release       (0x80000c90)  a0 = &log (own auipc/addi pair)
       +0xc2  jal bread         (0x80002b36)  a0 = log.dev,
                                              a1 = log.start+tail+1  -> "to",
                                              parked in s1 at +0xc6
       +0xd0  jal bread         (0x80002b36)  a0 = log.dev,
                                              a1 = log.lh.block[tail] -> "from",
                                              parked in s3 at +0xd4
       +0xe2  jal memmove       (0x80000d28)  a0 = s1+88 (to->data),
                                              a1 = a0+88 (from->data), a2 = 1024
       +0xe8  jal bwrite        (0x80002c0c)  a0 = s1 (to)
       +0xee  jal brelse        (0x80002c3e)  a0 = s3 (from)
       +0xf4  jal brelse        (0x80002c3e)  a0 = s1 (to)
       +0x104 jal write_head    (0x80003a2e)  no arguments
       +0x10a jal install_trans (0x80003a8c)  a0 = 0  (recovering = 0)
       +0x116 jal write_head    (0x80003a2e)  no arguments
     PANIC SITE: one, at +0x6e..+0x76 -- [auipc a0,0x4 ; addi a0,a0,-1976]
       materialises 0x80007500 = "log.committing", then [jal panic].  It is the
       arm taken when log.committing was already set on entry.  panic never
       returns, so the three [sd s3/s4/s5] at +0x68..+0x6c that precede it are
       dead stores kept only by gcc's shrink-wrapping.
     Loop (the inlined [write_log]'s [for (tail = 0; tail < log.lh.n; tail++)]):
       guard   +0x3e  bgtz a5 -> +0x9e     (a5 = log.lh.n; n <= 0: no copy)
       setup   +0x9e..+0xb0 (save s3/s4/s5, s5 = &log.lh.block[0], s4 = &log)
       top     +0xb4  (entered by falling through from +0xb0 -- do-while shape)
       bump    +0xf8  addiw s2,s2,1 ; +0xfa  addi s5,s5,4
       back    +0x100 blt s2,a5 -> +0xb4   (a5 = log.lh.n reloaded at +0xfc)
       exit    +0x104 (fall-through, into the write_head/install_trans tail)
       induction variable: s2 (tail), with s5 = &log.lh.block[tail] in lock step.
     Branch structure (the four arms of the function):
       +0x24  bnez a5 -> +0x68    log.committing set on entry: PANIC
       +0x26  bnez s2 -> +0x7a    outstanding != 0: wakeup + release + return
       +0x3e  bgtz a5 -> +0x9e    log.lh.n > 0: run the commit body
       +0x66  j      -> +0x92     commit-done tail joins the epilogue
       +0x100 blt s2,a5 -> +0xb4  the copy loop's back edge
       +0x120 j      -> +0x42     the commit body rejoins the "clear committing,
                                  bump ncommit, wakeup, release" tail
     Return sites: one, the [c.ret] at +0x9c (plus the non-returning panic).
     Every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (28 words):
         0x7139, 0xfc06, 0xf822, 0xf426, 0xf04a, 0x0080, 0x8526, 0x37fd,
         0x893e, 0x4785, 0x2785, 0xec4e, 0xe852, 0xe456, 0x70e2, 0x7442,
         0x74a2, 0x7902, 0x6121, 0x8082, 0x84aa, 0x89aa, 0x854e, 0x2905,
         0x4501, 0x69e2, 0x6a42, 0x6aa2
     * KernelBaseDecode.v (3 words):
         0x0001e497, 0x0001e517, 0x0001e797

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0x549c -- also CodeKilled.v:kldec_lw_killed
     0xd49c -- also CodeSleeplock.v:sldec_sw_a5_pid
     0xa035 -- also CodeCopyin.v:cidc_a035
     0x00004517 -- also CodeBread.v:bddb_00004517
     0x64850513 -- also CodeBread.v:bddb_64850513
     0x0001ea97 -- also CodeVirtioDiskRw.v:rwb_0001ea97
     0x40000613 -- also CodeVirtioDiskRw.v:rwb_40000613
   Also duplicated WITHIN the six new log.c decode files (same argument --
   these are the strongest promotion candidates):
     0x509c (+ begin_op), 0x018a2583 (+ install_trans),
     0x2585 (+ install_trans), 0x024a2503 (+ install_trans),
     0x000aa583 (+ install_trans), 0x0a91 (+ install_trans),
     0x02ca2783 (+ install_trans)
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
(* Compressed decode facts private to end_op.                    *)
(* ===================================================================== *)

(* 0x4cdc  lw a5,28(s1) *)
Lemma eodc_4cdc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4cdc : mword 16)) s
  = Some (C_LW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xccdc  sw a5,28(s1) *)
Lemma eodc_ccdc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xccdc : mword 16)) s
  = Some (C_SW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x509c  lw a5,32(s1) *)
Lemma eodc_509c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x509c : mword 16)) s
  = Some (C_LW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xe3b1  bnez a5,80003cb2 <end_op+0x68> *)
Lemma eodc_e3b1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe3b1 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 34, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd09c  sw a5,32(s1) *)
Lemma eodc_d09c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd09c : mword 16)) s
  = Some (C_SW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x54dc  lw a5,44(s1) *)
Lemma eodc_54dc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x54dc : mword 16)) s
  = Some (C_LW (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x549c  lw a5,40(s1) *)
Lemma eodc_549c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x549c : mword 16)) s
  = Some (C_LW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd49c  sw a5,40(s1) *)
Lemma eodc_d49c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd49c : mword 16)) s
  = Some (C_SW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa035  j 80003cdc <end_op+0x92> *)
Lemma eodc_a035 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa035 : mword 16)) s
  = Some (C_J (mword_of_int 22), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2585  addiw a1,a1,1 *)
Lemma eodc_2585 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2585 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0a91  addi s5,s5,4 *)
Lemma eodc_0a91 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0a91 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb70d  j 80003c8c <end_op+0x42> *)
Lemma eodc_b70d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb70d : mword 16)) s
  = Some (C_J (mword_of_int 1937), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma eocx_4cdc s :
  exec (execute (C_LW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_ccdc s :
  exec (execute (C_SW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 28, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_509c s :
  exec (execute (C_LW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_d09c s :
  exec (execute (C_SW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 32, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_54dc s :
  exec (execute (C_LW (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_549c s :
  exec (execute (C_LW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma eocx_d49c s :
  exec (execute (C_SW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to end_op.                  *)
(* ===================================================================== *)

(* 0x6c248493  addi s1,s1,1730 # 80022318 <log> *)
Lemma eodb_6c248493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6c248493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1730 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfa9fc0ef  jal 80000c08 <acquire> *)
Lemma eodb_fa9fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa9fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084776 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x04091a63  bnez s2,80003cc4 <end_op+0x7a> *)
Lemma eodb_04091a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04091a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0x6a448493  addi s1,s1,1700 # 80022318 <log> *)
Lemma eodb_6a448493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6a448493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1700 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x80efd0ef  jal 80000c90 <release> *)
Lemma eodb_80efd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x80efd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084878 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x06f04063  bgtz a5,80003ce8 <end_op+0x9e> *)
Lemma eodb_06f04063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06f04063 : mword 32)) s
  = Some (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BLT), s).
Proof. decode_bridge_ms. Qed.

(* 0x68c48493  addi s1,s1,1676 # 80022318 <log> *)
Lemma eodb_68c48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x68c48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1676 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xf73fc0ef  jal 80000c08 <acquire> *)
Lemma eodb_f73fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf73fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084722 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0204a023  sw zero,32(s1) *)
Lemma eodb_0204a023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0204a023 : mword 32)) s
  = Some (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xaacfe0ef  jal 80001f52 <wakeup> *)
Lemma eodb_aacfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xaacfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089644 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfe5fc0ef  jal 80000c90 <release> *)
Lemma eodb_fe5fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe5fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084836 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x00004517  auipc a0,0x4 *)
Lemma eodb_00004517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004517 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x84850513  addi a0,a0,-1976 # 80007500 <etext+0x500> *)
Lemma eodb_84850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x84850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2120 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xb67fc0ef  jal 80000826 <panic> *)
Lemma eodb_b67fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb67fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083686 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x65450513  addi a0,a0,1620 # 80022318 <log> *)
Lemma eodb_65450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x65450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1620 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xa86fe0ef  jal 80001f52 <wakeup> *)
Lemma eodb_a86fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa86fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089606 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x64850513  addi a0,a0,1608 # 80022318 <log> *)
Lemma eodb_64850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x64850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfb9fc0ef  jal 80000c90 <release> *)
Lemma eodb_fb9fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfb9fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084792 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001ea97  auipc s5,0x1e *)
Lemma eodb_0001ea97 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001ea97 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x65aa8a93  addi s5,s5,1626 # 80022348 <log+0x30> *)
Lemma eodb_65aa8a93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x65aa8a93 : mword 32)) s
  = Some (ITYPE (mword_of_int 1626 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001ea17  auipc s4,0x1e *)
Lemma eodb_0001ea17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001ea17 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x622a0a13  addi s4,s4,1570 # 80022318 <log> *)
Lemma eodb_622a0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x622a0a13 : mword 32)) s
  = Some (ITYPE (mword_of_int 1570 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x018a2583  lw a1,24(s4) *)
Lemma eodb_018a2583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x018a2583 : mword 32)) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x012585bb  addw a1,a1,s2 *)
Lemma eodb_012585bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x012585bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW), s).
Proof. decode_bridge_ms. Qed.

(* 0x024a2503  lw a0,36(s4) *)
Lemma eodb_024a2503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x024a2503 : mword 32)) s
  = Some (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xe2bfe0ef  jal 80002b36 <bread> *)
Lemma eodb_e2bfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe2bfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092586 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x000aa583  lw a1,0(s5) *)
Lemma eodb_000aa583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000aa583 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xe1dfe0ef  jal 80002b36 <bread> *)
Lemma eodb_e1dfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe1dfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092572 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x40000613  li a2,1024 *)
Lemma eodb_40000613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40000613 : mword 32)) s
  = Some (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x05850593  addi a1,a0,88 *)
Lemma eodb_05850593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05850593 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x05848513  addi a0,s1,88 *)
Lemma eodb_05848513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05848513 : mword 32)) s
  = Some (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xffdfc0ef  jal 80000d28 <memmove> *)
Lemma eodb_ffdfc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xffdfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084860 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xedbfe0ef  jal 80002c0c <bwrite> *)
Lemma eodb_edbfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xedbfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092762 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xf07fe0ef  jal 80002c3e <brelse> *)
Lemma eodb_f07fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf07fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092806 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xf01fe0ef  jal 80002c3e <brelse> *)
Lemma eodb_f01fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf01fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092800 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x02ca2783  lw a5,44(s4) *)
Lemma eodb_02ca2783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02ca2783 : mword 32)) s
  = Some (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xfaf94ae3  blt s2,a5,80003cfe <end_op+0xb4> *)
Lemma eodb_faf94ae3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaf94ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8116 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLT), s).
Proof. decode_bridge_ms. Qed.

(* 0xce1ff0ef  jal 80003a2e <write_head> *)
Lemma eodb_ce1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xce1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096352 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xd39ff0ef  jal 80003a8c <install_trans> *)
Lemma eodb_d39ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd39ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096440 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x5e07a623  sw zero,1516(a5) # 80022344 <log+0x2c> *)
Lemma eodb_5e07a623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5e07a623 : mword 32)) s
  = Some (STORE (mword_of_int 1516 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xccfff0ef  jal 80003a2e <write_head> *)
Lemma eodb_ccfff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xccfff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096334 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section EndOpInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation EO := KernelSyms.end_op.

  (* 0x00  7139  addi sp,sp,-64 *)
  Lemma eoi_00 : kernel_text -∗ instr (mword_of_int (EO + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (EO + 0x00)%Z (mword_of_int 0x7139 : mword 16)
    (mword_of_int (EO + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  (* 0x02  fc06  sd ra,56(sp) *)
  Lemma eoi_02 : kernel_text -∗ instr (mword_of_int (EO + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (EO + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (EO + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  (* 0x04  f822  sd s0,48(sp) *)
  Lemma eoi_04 : kernel_text -∗ instr (mword_of_int (EO + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (EO + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (EO + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  (* 0x06  f426  sd s1,40(sp) *)
  Lemma eoi_06 : kernel_text -∗ instr (mword_of_int (EO + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (EO + 0x06)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (EO + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  (* 0x08  f04a  sd s2,32(sp) *)
  Lemma eoi_08 : kernel_text -∗ instr (mword_of_int (EO + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (EO + 0x08)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (EO + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  (* 0x0a  0080  addi s0,sp,64 *)
  Lemma eoi_0a : kernel_text -∗ instr (mword_of_int (EO + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (EO + 0x0a)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (EO + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0c  0001e497  auipc s1,0x1e *)
  Lemma eoi_0c : kernel_text -∗ instr (mword_of_int (EO + 0x0c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (EO + 0x0c)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (EO + 0x0c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  (* 0x10  6c248493  addi s1,s1,1730 # 80022318 <log> *)
  Lemma eoi_10 : kernel_text -∗ instr (mword_of_int (EO + 0x10) : mword 64) false (ITYPE (mword_of_int 1730 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (EO + 0x10)%Z (mword_of_int 0x6c248493 : mword 32)
    (mword_of_int (EO + 0x10) : mword 64) (ITYPE (mword_of_int 1730 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) eodb_6c248493. Qed.

  (* 0x14  8526  mv a0,s1 *)
  Lemma eoi_14 : kernel_text -∗ instr (mword_of_int (EO + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0x14)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x16  fa9fc0ef  jal 80000c08 <acquire> *)
  Lemma eoi_16 : kernel_text -∗ instr (mword_of_int (EO + 0x16) : mword 64) false (JAL (mword_of_int 2084776 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x16)%Z (mword_of_int 0xfa9fc0ef : mword 32)
    (mword_of_int (EO + 0x16) : mword 64) (JAL (mword_of_int 2084776 : mword 21, Regidx (mword_of_int 1))) eodb_fa9fc0ef. Qed.

  (* 0x1a  4cdc  lw a5,28(s1) *)
  Lemma eoi_1a : kernel_text -∗ instr (mword_of_int (EO + 0x1a) : mword 64) true (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (EO + 0x1a)%Z (mword_of_int 0x4cdc : mword 16)
    (mword_of_int (EO + 0x1a) : mword 64) (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) eodc_4cdc eocx_4cdc. Qed.

  (* 0x1c  37fd  addiw a5,a5,-1 *)
  Lemma eoi_1c : kernel_text -∗ instr (mword_of_int (EO + 0x1c) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (EO + 0x1c)%Z (mword_of_int 0x37fd : mword 16)
    (mword_of_int (EO + 0x1c) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_37fd exec_execute_C_ADDIW. Qed.

  (* 0x1e  893e  mv s2,a5 *)
  Lemma eoi_1e : kernel_text -∗ instr (mword_of_int (EO + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (EO + 0x1e)%Z (mword_of_int 0x893e : mword 16)
    (mword_of_int (EO + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 18), ADD)) cdec_893e exec_execute_C_MV. Qed.

  (* 0x20  ccdc  sw a5,28(s1) *)
  Lemma eoi_20 : kernel_text -∗ instr (mword_of_int (EO + 0x20) : mword 64) true (STORE (mword_of_int 28, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (EO + 0x20)%Z (mword_of_int 0xccdc : mword 16)
    (mword_of_int (EO + 0x20) : mword 64) (STORE (mword_of_int 28, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) eodc_ccdc eocx_ccdc. Qed.

  (* 0x22  509c  lw a5,32(s1) *)
  Lemma eoi_22 : kernel_text -∗ instr (mword_of_int (EO + 0x22) : mword 64) true (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (EO + 0x22)%Z (mword_of_int 0x509c : mword 16)
    (mword_of_int (EO + 0x22) : mword 64) (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) eodc_509c eocx_509c. Qed.

  (* 0x24  e3b1  bnez a5,80003cb2 <end_op+0x68> *)
  Lemma eoi_24 : kernel_text -∗ instr (mword_of_int (EO + 0x24) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 34 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (EO + 0x24)%Z (mword_of_int 0xe3b1 : mword 16)
    (mword_of_int (EO + 0x24) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 34 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) eodc_e3b1 exec_execute_C_BNEZ. Qed.

  (* 0x26  04091a63  bnez s2,80003cc4 <end_op+0x7a> *)
  Lemma eoi_26 : kernel_text -∗ instr (mword_of_int (EO + 0x26) : mword 64) false (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BNE)).
  Proof. mk_base (EO + 0x26)%Z (mword_of_int 0x04091a63 : mword 32)
    (mword_of_int (EO + 0x26) : mword 64) (BTYPE (mword_of_int 84 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BNE)) eodb_04091a63. Qed.

  (* 0x2a  0001e497  auipc s1,0x1e *)
  Lemma eoi_2a : kernel_text -∗ instr (mword_of_int (EO + 0x2a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (EO + 0x2a)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (EO + 0x2a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  (* 0x2e  6a448493  addi s1,s1,1700 # 80022318 <log> *)
  Lemma eoi_2e : kernel_text -∗ instr (mword_of_int (EO + 0x2e) : mword 64) false (ITYPE (mword_of_int 1700 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (EO + 0x2e)%Z (mword_of_int 0x6a448493 : mword 32)
    (mword_of_int (EO + 0x2e) : mword 64) (ITYPE (mword_of_int 1700 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) eodb_6a448493. Qed.

  (* 0x32  4785  li a5,1 *)
  Lemma eoi_32 : kernel_text -∗ instr (mword_of_int (EO + 0x32) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (EO + 0x32)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (EO + 0x32) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  (* 0x34  d09c  sw a5,32(s1) *)
  Lemma eoi_34 : kernel_text -∗ instr (mword_of_int (EO + 0x34) : mword 64) true (STORE (mword_of_int 32, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (EO + 0x34)%Z (mword_of_int 0xd09c : mword 16)
    (mword_of_int (EO + 0x34) : mword 64) (STORE (mword_of_int 32, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) eodc_d09c eocx_d09c. Qed.

  (* 0x36  8526  mv a0,s1 *)
  Lemma eoi_36 : kernel_text -∗ instr (mword_of_int (EO + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0x36)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x38  80efd0ef  jal 80000c90 <release> *)
  Lemma eoi_38 : kernel_text -∗ instr (mword_of_int (EO + 0x38) : mword 64) false (JAL (mword_of_int 2084878 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x38)%Z (mword_of_int 0x80efd0ef : mword 32)
    (mword_of_int (EO + 0x38) : mword 64) (JAL (mword_of_int 2084878 : mword 21, Regidx (mword_of_int 1))) eodb_80efd0ef. Qed.

  (* 0x3c  54dc  lw a5,44(s1) *)
  Lemma eoi_3c : kernel_text -∗ instr (mword_of_int (EO + 0x3c) : mword 64) true (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (EO + 0x3c)%Z (mword_of_int 0x54dc : mword 16)
    (mword_of_int (EO + 0x3c) : mword 64) (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) eodc_54dc eocx_54dc. Qed.

  (* 0x3e  06f04063  bgtz a5,80003ce8 <end_op+0x9e> *)
  Lemma eoi_3e : kernel_text -∗ instr (mword_of_int (EO + 0x3e) : mword 64) false (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BLT)).
  Proof. mk_base (EO + 0x3e)%Z (mword_of_int 0x06f04063 : mword 32)
    (mword_of_int (EO + 0x3e) : mword 64) (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BLT)) eodb_06f04063. Qed.

  (* 0x42  0001e497  auipc s1,0x1e *)
  Lemma eoi_42 : kernel_text -∗ instr (mword_of_int (EO + 0x42) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (EO + 0x42)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (EO + 0x42) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  (* 0x46  68c48493  addi s1,s1,1676 # 80022318 <log> *)
  Lemma eoi_46 : kernel_text -∗ instr (mword_of_int (EO + 0x46) : mword 64) false (ITYPE (mword_of_int 1676 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (EO + 0x46)%Z (mword_of_int 0x68c48493 : mword 32)
    (mword_of_int (EO + 0x46) : mword 64) (ITYPE (mword_of_int 1676 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) eodb_68c48493. Qed.

  (* 0x4a  8526  mv a0,s1 *)
  Lemma eoi_4a : kernel_text -∗ instr (mword_of_int (EO + 0x4a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0x4a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x4c  f73fc0ef  jal 80000c08 <acquire> *)
  Lemma eoi_4c : kernel_text -∗ instr (mword_of_int (EO + 0x4c) : mword 64) false (JAL (mword_of_int 2084722 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x4c)%Z (mword_of_int 0xf73fc0ef : mword 32)
    (mword_of_int (EO + 0x4c) : mword 64) (JAL (mword_of_int 2084722 : mword 21, Regidx (mword_of_int 1))) eodb_f73fc0ef. Qed.

  (* 0x50  0204a023  sw zero,32(s1) *)
  Lemma eoi_50 : kernel_text -∗ instr (mword_of_int (EO + 0x50) : mword 64) false (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (EO + 0x50)%Z (mword_of_int 0x0204a023 : mword 32)
    (mword_of_int (EO + 0x50) : mword 64) (STORE (mword_of_int 32 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) eodb_0204a023. Qed.

  (* 0x54  549c  lw a5,40(s1) *)
  Lemma eoi_54 : kernel_text -∗ instr (mword_of_int (EO + 0x54) : mword 64) true (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (EO + 0x54)%Z (mword_of_int 0x549c : mword 16)
    (mword_of_int (EO + 0x54) : mword 64) (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) eodc_549c eocx_549c. Qed.

  (* 0x56  2785  addiw a5,a5,1 *)
  Lemma eoi_56 : kernel_text -∗ instr (mword_of_int (EO + 0x56) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (EO + 0x56)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (EO + 0x56) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  (* 0x58  d49c  sw a5,40(s1) *)
  Lemma eoi_58 : kernel_text -∗ instr (mword_of_int (EO + 0x58) : mword 64) true (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (EO + 0x58)%Z (mword_of_int 0xd49c : mword 16)
    (mword_of_int (EO + 0x58) : mword 64) (STORE (mword_of_int 40, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) eodc_d49c eocx_d49c. Qed.

  (* 0x5a  8526  mv a0,s1 *)
  Lemma eoi_5a : kernel_text -∗ instr (mword_of_int (EO + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0x5a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x5c  aacfe0ef  jal 80001f52 <wakeup> *)
  Lemma eoi_5c : kernel_text -∗ instr (mword_of_int (EO + 0x5c) : mword 64) false (JAL (mword_of_int 2089644 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x5c)%Z (mword_of_int 0xaacfe0ef : mword 32)
    (mword_of_int (EO + 0x5c) : mword 64) (JAL (mword_of_int 2089644 : mword 21, Regidx (mword_of_int 1))) eodb_aacfe0ef. Qed.

  (* 0x60  8526  mv a0,s1 *)
  Lemma eoi_60 : kernel_text -∗ instr (mword_of_int (EO + 0x60) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0x60)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0x60) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x62  fe5fc0ef  jal 80000c90 <release> *)
  Lemma eoi_62 : kernel_text -∗ instr (mword_of_int (EO + 0x62) : mword 64) false (JAL (mword_of_int 2084836 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x62)%Z (mword_of_int 0xfe5fc0ef : mword 32)
    (mword_of_int (EO + 0x62) : mword 64) (JAL (mword_of_int 2084836 : mword 21, Regidx (mword_of_int 1))) eodb_fe5fc0ef. Qed.

  (* 0x66  a035  j 80003cdc <end_op+0x92> *)
  Lemma eoi_66 : kernel_text -∗ instr (mword_of_int (EO + 0x66) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (EO + 0x66)%Z (mword_of_int 0xa035 : mword 16)
    (mword_of_int (EO + 0x66) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")), zreg)) eodc_a035 exec_execute_C_J. Qed.

  (* 0x68  ec4e  sd s3,24(sp) *)
  Lemma eoi_68 : kernel_text -∗ instr (mword_of_int (EO + 0x68) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (EO + 0x68)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (EO + 0x68) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  (* 0x6a  e852  sd s4,16(sp) *)
  Lemma eoi_6a : kernel_text -∗ instr (mword_of_int (EO + 0x6a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (EO + 0x6a)%Z (mword_of_int 0xe852 : mword 16)
    (mword_of_int (EO + 0x6a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.

  (* 0x6c  e456  sd s5,8(sp) *)
  Lemma eoi_6c : kernel_text -∗ instr (mword_of_int (EO + 0x6c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (EO + 0x6c)%Z (mword_of_int 0xe456 : mword 16)
    (mword_of_int (EO + 0x6c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.

  (* 0x6e  00004517  auipc a0,0x4 *)
  Lemma eoi_6e : kernel_text -∗ instr (mword_of_int (EO + 0x6e) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (EO + 0x6e)%Z (mword_of_int 0x00004517 : mword 32)
    (mword_of_int (EO + 0x6e) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)) eodb_00004517. Qed.

  (* 0x72  84850513  addi a0,a0,-1976 # 80007500 <etext+0x500> *)
  Lemma eoi_72 : kernel_text -∗ instr (mword_of_int (EO + 0x72) : mword 64) false (ITYPE (mword_of_int 2120 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (EO + 0x72)%Z (mword_of_int 0x84850513 : mword 32)
    (mword_of_int (EO + 0x72) : mword 64) (ITYPE (mword_of_int 2120 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) eodb_84850513. Qed.

  (* 0x76  b67fc0ef  jal 80000826 <panic> *)
  Lemma eoi_76 : kernel_text -∗ instr (mword_of_int (EO + 0x76) : mword 64) false (JAL (mword_of_int 2083686 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x76)%Z (mword_of_int 0xb67fc0ef : mword 32)
    (mword_of_int (EO + 0x76) : mword 64) (JAL (mword_of_int 2083686 : mword 21, Regidx (mword_of_int 1))) eodb_b67fc0ef. Qed.

  (* 0x7a  0001e517  auipc a0,0x1e *)
  Lemma eoi_7a : kernel_text -∗ instr (mword_of_int (EO + 0x7a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (EO + 0x7a)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (EO + 0x7a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x7e  65450513  addi a0,a0,1620 # 80022318 <log> *)
  Lemma eoi_7e : kernel_text -∗ instr (mword_of_int (EO + 0x7e) : mword 64) false (ITYPE (mword_of_int 1620 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (EO + 0x7e)%Z (mword_of_int 0x65450513 : mword 32)
    (mword_of_int (EO + 0x7e) : mword 64) (ITYPE (mword_of_int 1620 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) eodb_65450513. Qed.

  (* 0x82  a86fe0ef  jal 80001f52 <wakeup> *)
  Lemma eoi_82 : kernel_text -∗ instr (mword_of_int (EO + 0x82) : mword 64) false (JAL (mword_of_int 2089606 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x82)%Z (mword_of_int 0xa86fe0ef : mword 32)
    (mword_of_int (EO + 0x82) : mword 64) (JAL (mword_of_int 2089606 : mword 21, Regidx (mword_of_int 1))) eodb_a86fe0ef. Qed.

  (* 0x86  0001e517  auipc a0,0x1e *)
  Lemma eoi_86 : kernel_text -∗ instr (mword_of_int (EO + 0x86) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (EO + 0x86)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (EO + 0x86) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x8a  64850513  addi a0,a0,1608 # 80022318 <log> *)
  Lemma eoi_8a : kernel_text -∗ instr (mword_of_int (EO + 0x8a) : mword 64) false (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (EO + 0x8a)%Z (mword_of_int 0x64850513 : mword 32)
    (mword_of_int (EO + 0x8a) : mword 64) (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) eodb_64850513. Qed.

  (* 0x8e  fb9fc0ef  jal 80000c90 <release> *)
  Lemma eoi_8e : kernel_text -∗ instr (mword_of_int (EO + 0x8e) : mword 64) false (JAL (mword_of_int 2084792 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x8e)%Z (mword_of_int 0xfb9fc0ef : mword 32)
    (mword_of_int (EO + 0x8e) : mword 64) (JAL (mword_of_int 2084792 : mword 21, Regidx (mword_of_int 1))) eodb_fb9fc0ef. Qed.

  (* 0x92  70e2  ld ra,56(sp) *)
  Lemma eoi_92 : kernel_text -∗ instr (mword_of_int (EO + 0x92) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (EO + 0x92)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (EO + 0x92) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  (* 0x94  7442  ld s0,48(sp) *)
  Lemma eoi_94 : kernel_text -∗ instr (mword_of_int (EO + 0x94) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (EO + 0x94)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (EO + 0x94) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  (* 0x96  74a2  ld s1,40(sp) *)
  Lemma eoi_96 : kernel_text -∗ instr (mword_of_int (EO + 0x96) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (EO + 0x96)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (EO + 0x96) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  (* 0x98  7902  ld s2,32(sp) *)
  Lemma eoi_98 : kernel_text -∗ instr (mword_of_int (EO + 0x98) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (EO + 0x98)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (EO + 0x98) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  (* 0x9a  6121  addi sp,sp,64 *)
  Lemma eoi_9a : kernel_text -∗ instr (mword_of_int (EO + 0x9a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (EO + 0x9a)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (EO + 0x9a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  (* 0x9c  8082  ret *)
  Lemma eoi_9c : kernel_text -∗ instr (mword_of_int (EO + 0x9c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (EO + 0x9c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (EO + 0x9c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* 0x9e  ec4e  sd s3,24(sp) *)
  Lemma eoi_9e : kernel_text -∗ instr (mword_of_int (EO + 0x9e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (EO + 0x9e)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (EO + 0x9e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  (* 0xa0  e852  sd s4,16(sp) *)
  Lemma eoi_a0 : kernel_text -∗ instr (mword_of_int (EO + 0xa0) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (EO + 0xa0)%Z (mword_of_int 0xe852 : mword 16)
    (mword_of_int (EO + 0xa0) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.

  (* 0xa2  e456  sd s5,8(sp) *)
  Lemma eoi_a2 : kernel_text -∗ instr (mword_of_int (EO + 0xa2) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (EO + 0xa2)%Z (mword_of_int 0xe456 : mword 16)
    (mword_of_int (EO + 0xa2) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.

  (* 0xa4  0001ea97  auipc s5,0x1e *)
  Lemma eoi_a4 : kernel_text -∗ instr (mword_of_int (EO + 0xa4) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC)).
  Proof. mk_base (EO + 0xa4)%Z (mword_of_int 0x0001ea97 : mword 32)
    (mword_of_int (EO + 0xa4) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 21), AUIPC)) eodb_0001ea97. Qed.

  (* 0xa8  65aa8a93  addi s5,s5,1626 # 80022348 <log+0x30> *)
  Lemma eoi_a8 : kernel_text -∗ instr (mword_of_int (EO + 0xa8) : mword 64) false (ITYPE (mword_of_int 1626 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).
  Proof. mk_base (EO + 0xa8)%Z (mword_of_int 0x65aa8a93 : mword 32)
    (mword_of_int (EO + 0xa8) : mword 64) (ITYPE (mword_of_int 1626 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) eodb_65aa8a93. Qed.

  (* 0xac  0001ea17  auipc s4,0x1e *)
  Lemma eoi_ac : kernel_text -∗ instr (mword_of_int (EO + 0xac) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (EO + 0xac)%Z (mword_of_int 0x0001ea17 : mword 32)
    (mword_of_int (EO + 0xac) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 20), AUIPC)) eodb_0001ea17. Qed.

  (* 0xb0  622a0a13  addi s4,s4,1570 # 80022318 <log> *)
  Lemma eoi_b0 : kernel_text -∗ instr (mword_of_int (EO + 0xb0) : mword 64) false (ITYPE (mword_of_int 1570 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (EO + 0xb0)%Z (mword_of_int 0x622a0a13 : mword 32)
    (mword_of_int (EO + 0xb0) : mword 64) (ITYPE (mword_of_int 1570 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) eodb_622a0a13. Qed.

  (* 0xb4  018a2583  lw a1,24(s4) *)
  Lemma eoi_b4 : kernel_text -∗ instr (mword_of_int (EO + 0xb4) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (EO + 0xb4)%Z (mword_of_int 0x018a2583 : mword 32)
    (mword_of_int (EO + 0xb4) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 11), false, 4)) eodb_018a2583. Qed.

  (* 0xb8  012585bb  addw a1,a1,s2 *)
  Lemma eoi_b8 : kernel_text -∗ instr (mword_of_int (EO + 0xb8) : mword 64) false (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW)).
  Proof. mk_base (EO + 0xb8)%Z (mword_of_int 0x012585bb : mword 32)
    (mword_of_int (EO + 0xb8) : mword 64) (RTYPEW (Regidx (mword_of_int 18), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDW)) eodb_012585bb. Qed.

  (* 0xbc  2585  addiw a1,a1,1 *)
  Lemma eoi_bc : kernel_text -∗ instr (mword_of_int (EO + 0xbc) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11))).
  Proof. mk_rvc (EO + 0xbc)%Z (mword_of_int 0x2585 : mword 16)
    (mword_of_int (EO + 0xbc) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11))) eodc_2585 exec_execute_C_ADDIW. Qed.

  (* 0xbe  024a2503  lw a0,36(s4) *)
  Lemma eoi_be : kernel_text -∗ instr (mword_of_int (EO + 0xbe) : mword 64) false (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (EO + 0xbe)%Z (mword_of_int 0x024a2503 : mword 32)
    (mword_of_int (EO + 0xbe) : mword 64) (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)) eodb_024a2503. Qed.

  (* 0xc2  e2bfe0ef  jal 80002b36 <bread> *)
  Lemma eoi_c2 : kernel_text -∗ instr (mword_of_int (EO + 0xc2) : mword 64) false (JAL (mword_of_int 2092586 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xc2)%Z (mword_of_int 0xe2bfe0ef : mword 32)
    (mword_of_int (EO + 0xc2) : mword 64) (JAL (mword_of_int 2092586 : mword 21, Regidx (mword_of_int 1))) eodb_e2bfe0ef. Qed.

  (* 0xc6  84aa  mv s1,a0 *)
  Lemma eoi_c6 : kernel_text -∗ instr (mword_of_int (EO + 0xc6) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (EO + 0xc6)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (EO + 0xc6) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0xc8  000aa583  lw a1,0(s5) *)
  Lemma eoi_c8 : kernel_text -∗ instr (mword_of_int (EO + 0xc8) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (EO + 0xc8)%Z (mword_of_int 0x000aa583 : mword 32)
    (mword_of_int (EO + 0xc8) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 11), false, 4)) eodb_000aa583. Qed.

  (* 0xcc  024a2503  lw a0,36(s4) *)
  Lemma eoi_cc : kernel_text -∗ instr (mword_of_int (EO + 0xcc) : mword 64) false (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (EO + 0xcc)%Z (mword_of_int 0x024a2503 : mword 32)
    (mword_of_int (EO + 0xcc) : mword 64) (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 4)) eodb_024a2503. Qed.

  (* 0xd0  e1dfe0ef  jal 80002b36 <bread> *)
  Lemma eoi_d0 : kernel_text -∗ instr (mword_of_int (EO + 0xd0) : mword 64) false (JAL (mword_of_int 2092572 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xd0)%Z (mword_of_int 0xe1dfe0ef : mword 32)
    (mword_of_int (EO + 0xd0) : mword 64) (JAL (mword_of_int 2092572 : mword 21, Regidx (mword_of_int 1))) eodb_e1dfe0ef. Qed.

  (* 0xd4  89aa  mv s3,a0 *)
  Lemma eoi_d4 : kernel_text -∗ instr (mword_of_int (EO + 0xd4) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (EO + 0xd4)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (EO + 0xd4) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  (* 0xd6  40000613  li a2,1024 *)
  Lemma eoi_d6 : kernel_text -∗ instr (mword_of_int (EO + 0xd6) : mword 64) false (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (EO + 0xd6)%Z (mword_of_int 0x40000613 : mword 32)
    (mword_of_int (EO + 0xd6) : mword 64) (ITYPE (mword_of_int 1024 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)) eodb_40000613. Qed.

  (* 0xda  05850593  addi a1,a0,88 *)
  Lemma eoi_da : kernel_text -∗ instr (mword_of_int (EO + 0xda) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (EO + 0xda)%Z (mword_of_int 0x05850593 : mword 32)
    (mword_of_int (EO + 0xda) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 11), ADDI)) eodb_05850593. Qed.

  (* 0xde  05848513  addi a0,s1,88 *)
  Lemma eoi_de : kernel_text -∗ instr (mword_of_int (EO + 0xde) : mword 64) false (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (EO + 0xde)%Z (mword_of_int 0x05848513 : mword 32)
    (mword_of_int (EO + 0xde) : mword 64) (ITYPE (mword_of_int 88 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) eodb_05848513. Qed.

  (* 0xe2  ffdfc0ef  jal 80000d28 <memmove> *)
  Lemma eoi_e2 : kernel_text -∗ instr (mword_of_int (EO + 0xe2) : mword 64) false (JAL (mword_of_int 2084860 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xe2)%Z (mword_of_int 0xffdfc0ef : mword 32)
    (mword_of_int (EO + 0xe2) : mword 64) (JAL (mword_of_int 2084860 : mword 21, Regidx (mword_of_int 1))) eodb_ffdfc0ef. Qed.

  (* 0xe6  8526  mv a0,s1 *)
  Lemma eoi_e6 : kernel_text -∗ instr (mword_of_int (EO + 0xe6) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0xe6)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0xe6) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0xe8  edbfe0ef  jal 80002c0c <bwrite> *)
  Lemma eoi_e8 : kernel_text -∗ instr (mword_of_int (EO + 0xe8) : mword 64) false (JAL (mword_of_int 2092762 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xe8)%Z (mword_of_int 0xedbfe0ef : mword 32)
    (mword_of_int (EO + 0xe8) : mword 64) (JAL (mword_of_int 2092762 : mword 21, Regidx (mword_of_int 1))) eodb_edbfe0ef. Qed.

  (* 0xec  854e  mv a0,s3 *)
  Lemma eoi_ec : kernel_text -∗ instr (mword_of_int (EO + 0xec) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0xec)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (EO + 0xec) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  (* 0xee  f07fe0ef  jal 80002c3e <brelse> *)
  Lemma eoi_ee : kernel_text -∗ instr (mword_of_int (EO + 0xee) : mword 64) false (JAL (mword_of_int 2092806 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xee)%Z (mword_of_int 0xf07fe0ef : mword 32)
    (mword_of_int (EO + 0xee) : mword 64) (JAL (mword_of_int 2092806 : mword 21, Regidx (mword_of_int 1))) eodb_f07fe0ef. Qed.

  (* 0xf2  8526  mv a0,s1 *)
  Lemma eoi_f2 : kernel_text -∗ instr (mword_of_int (EO + 0xf2) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (EO + 0xf2)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (EO + 0xf2) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0xf4  f01fe0ef  jal 80002c3e <brelse> *)
  Lemma eoi_f4 : kernel_text -∗ instr (mword_of_int (EO + 0xf4) : mword 64) false (JAL (mword_of_int 2092800 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0xf4)%Z (mword_of_int 0xf01fe0ef : mword 32)
    (mword_of_int (EO + 0xf4) : mword 64) (JAL (mword_of_int 2092800 : mword 21, Regidx (mword_of_int 1))) eodb_f01fe0ef. Qed.

  (* 0xf8  2905  addiw s2,s2,1 *)
  Lemma eoi_f8 : kernel_text -∗ instr (mword_of_int (EO + 0xf8) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))).
  Proof. mk_rvc (EO + 0xf8)%Z (mword_of_int 0x2905 : mword 16)
    (mword_of_int (EO + 0xf8) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18))) cdec_2905 exec_execute_C_ADDIW. Qed.

  (* 0xfa  0a91  addi s5,s5,4 *)
  Lemma eoi_fa : kernel_text -∗ instr (mword_of_int (EO + 0xfa) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc (EO + 0xfa)%Z (mword_of_int 0x0a91 : mword 16)
    (mword_of_int (EO + 0xfa) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADDI)) eodc_0a91 exec_execute_C_ADDI. Qed.

  (* 0xfc  02ca2783  lw a5,44(s4) *)
  Lemma eoi_fc : kernel_text -∗ instr (mword_of_int (EO + 0xfc) : mword 64) false (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (EO + 0xfc)%Z (mword_of_int 0x02ca2783 : mword 32)
    (mword_of_int (EO + 0xfc) : mword 64) (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 15), false, 4)) eodb_02ca2783. Qed.

  (* 0x100  faf94ae3  blt s2,a5,80003cfe <end_op+0xb4> *)
  Lemma eoi_100 : kernel_text -∗ instr (mword_of_int (EO + 0x100) : mword 64) false (BTYPE (mword_of_int 8116 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLT)).
  Proof. mk_base (EO + 0x100)%Z (mword_of_int 0xfaf94ae3 : mword 32)
    (mword_of_int (EO + 0x100) : mword 64) (BTYPE (mword_of_int 8116 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLT)) eodb_faf94ae3. Qed.

  (* 0x104  ce1ff0ef  jal 80003a2e <write_head> *)
  Lemma eoi_104 : kernel_text -∗ instr (mword_of_int (EO + 0x104) : mword 64) false (JAL (mword_of_int 2096352 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x104)%Z (mword_of_int 0xce1ff0ef : mword 32)
    (mword_of_int (EO + 0x104) : mword 64) (JAL (mword_of_int 2096352 : mword 21, Regidx (mword_of_int 1))) eodb_ce1ff0ef. Qed.

  (* 0x108  4501  li a0,0 *)
  Lemma eoi_108 : kernel_text -∗ instr (mword_of_int (EO + 0x108) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (EO + 0x108)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (EO + 0x108) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* 0x10a  d39ff0ef  jal 80003a8c <install_trans> *)
  Lemma eoi_10a : kernel_text -∗ instr (mword_of_int (EO + 0x10a) : mword 64) false (JAL (mword_of_int 2096440 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x10a)%Z (mword_of_int 0xd39ff0ef : mword 32)
    (mword_of_int (EO + 0x10a) : mword 64) (JAL (mword_of_int 2096440 : mword 21, Regidx (mword_of_int 1))) eodb_d39ff0ef. Qed.

  (* 0x10e  0001e797  auipc a5,0x1e *)
  Lemma eoi_10e : kernel_text -∗ instr (mword_of_int (EO + 0x10e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (EO + 0x10e)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (EO + 0x10e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x112  5e07a623  sw zero,1516(a5) # 80022344 <log+0x2c> *)
  Lemma eoi_112 : kernel_text -∗ instr (mword_of_int (EO + 0x112) : mword 64) false (STORE (mword_of_int 1516 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (EO + 0x112)%Z (mword_of_int 0x5e07a623 : mword 32)
    (mword_of_int (EO + 0x112) : mword 64) (STORE (mword_of_int 1516 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) eodb_5e07a623. Qed.

  (* 0x116  ccfff0ef  jal 80003a2e <write_head> *)
  Lemma eoi_116 : kernel_text -∗ instr (mword_of_int (EO + 0x116) : mword 64) false (JAL (mword_of_int 2096334 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (EO + 0x116)%Z (mword_of_int 0xccfff0ef : mword 32)
    (mword_of_int (EO + 0x116) : mword 64) (JAL (mword_of_int 2096334 : mword 21, Regidx (mword_of_int 1))) eodb_ccfff0ef. Qed.

  (* 0x11a  69e2  ld s3,24(sp) *)
  Lemma eoi_11a : kernel_text -∗ instr (mword_of_int (EO + 0x11a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (EO + 0x11a)%Z (mword_of_int 0x69e2 : mword 16)
    (mword_of_int (EO + 0x11a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.

  (* 0x11c  6a42  ld s4,16(sp) *)
  Lemma eoi_11c : kernel_text -∗ instr (mword_of_int (EO + 0x11c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (EO + 0x11c)%Z (mword_of_int 0x6a42 : mword 16)
    (mword_of_int (EO + 0x11c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a42 exec_execute_C_LDSP. Qed.

  (* 0x11e  6aa2  ld s5,8(sp) *)
  Lemma eoi_11e : kernel_text -∗ instr (mword_of_int (EO + 0x11e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (EO + 0x11e)%Z (mword_of_int 0x6aa2 : mword 16)
    (mword_of_int (EO + 0x11e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6aa2 exec_execute_C_LDSP. Qed.

  (* 0x120  b70d  j 80003c8c <end_op+0x42> *)
  Lemma eoi_120 : kernel_text -∗ instr (mword_of_int (EO + 0x120) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1937 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (EO + 0x120)%Z (mword_of_int 0xb70d : mword 16)
    (mword_of_int (EO + 0x120) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1937 : mword 11) ('b"0")), zreg)) eodc_b70d exec_execute_C_J. Qed.

End EndOpInstrs.

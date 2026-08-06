(* CodeInitlog.v -- the instruction-DECODE layer for xv6's initlog().
   For EVERY instruction of

     initlog @ 0x80003b58 .. 0x80003bd8   (offsets 0x00 .. 0x80, 130 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([ili_<off>]) plus
   the per-instruction decode facts they consume ([ildc_<word>] compressed /
   [ildb_<word>] base / [ilcx_<word>] the compressed leaf expansions).
   Both [read_head] and [recover_from_log] are [static] with initlog their only
   caller, so gcc INLINED them: this one function contains the initlock, the
   header read-back loop, the install_trans(1) recovery pass, the [log.lh.n = 0]
   clear and the final write_head.  The C's
   [if (sizeof(struct logheader) >= BSIZE) panic("initlog: too big logheader")]
   is a compile-time-false test and is NOT in the image -- initlog has no panic.

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

     0x00 7179     addi sp,sp,-48
     0x02 f406     sd ra,40(sp)
     0x04 f022     sd s0,32(sp)
     0x06 ec26     sd s1,24(sp)
     0x08 e84a     sd s2,16(sp)
     0x0a e44e     sd s3,8(sp)
     0x0c 1800     addi s0,sp,48
     0x0e 84aa     mv s1,a0
     0x10 89ae     mv s3,a1
     0x12 0001e917 auipc s2,0x1e
     0x16 7ae90913 addi s2,s2,1966 # 80022318 <log>
     0x1a 00004597 auipc a1,0x4
     0x1e 98658593 addi a1,a1,-1658 # 800074f8 <etext+0x4f8>
     0x22 854a     mv a0,s2
     0x24 80cfd0ef jal 80000b88 <initlock>
     0x28 0149a583 lw a1,20(s3)
     0x2c 00b92c23 sw a1,24(s2)
     0x30 02992223 sw s1,36(s2)
     0x34 8526     mv a0,s1
     0x36 fa9fe0ef jal 80002b36 <bread>
     0x3a 4d30     lw a2,88(a0)
     0x3c 02c92623 sw a2,44(s2)
     0x40 00c05f63 blez a2,80003bb6 <initlog+0x5e>
     0x44 87aa     mv a5,a0
     0x46 0001e717 auipc a4,0x1e
     0x4a 7aa70713 addi a4,a4,1962 # 80022348 <log+0x30>
     0x4e 060a     slli a2,a2,0x2
     0x50 962a     add a2,a2,a0
     0x52 4ff4     lw a3,92(a5)
     0x54 c314     sw a3,0(a4)
     0x56 0791     addi a5,a5,4
     0x58 0711     addi a4,a4,4
     0x5a fec79ce3 bne a5,a2,80003baa <initlog+0x52>
     0x5e 888ff0ef jal 80002c3e <brelse>
     0x62 4505     li a0,1
     0x64 ed1ff0ef jal 80003a8c <install_trans>
     0x68 0001e797 auipc a5,0x1e
     0x6c 7807a223 sw zero,1924(a5) # 80022344 <log+0x2c>
     0x70 e67ff0ef jal 80003a2e <write_head>
     0x74 70a2     ld ra,40(sp)
     0x76 7402     ld s0,32(sp)
     0x78 64e2     ld s1,24(sp)
     0x7a 6942     ld s2,16(sp)
     0x7c 69a2     ld s3,8(sp)
     0x7e 6145     addi sp,sp,48
     0x80 8082     ret

   STRUCTURE.
     Frame: 48 bytes ([c.addi16sp sp,-48] at +0x00, [c.addi16sp sp,48] at +0x7e).
       Saved: ra@40, s0@32, s1@24, s2@16, s3@8; s0 = sp+48.
     Register roles: s1 = the [dev] argument (from a0 at +0x0e); s3 = the
       [sb] argument (from a1 at +0x10); s2 = &log (0x80022318); a5 = the source
       cursor into buf; a4 = the destination cursor &log.lh.block[i]; a2 = first
       lh->n, then the end sentinel buf + 4*n; a3 = the word in flight.
     Log fields touched: WRITES log.start(+24) @+0x2c, log.dev(+36) @+0x30,
       log.lh.n(+44) @+0x3c and again (= 0) @+0x6c, log.lh.block[i](+48+4i)
       @+0x54.  The lock itself (+0..+23) is written by the initlock call.
     Superblock field: sb->logstart at 20(s3), read @+0x28.
     Buffer fields: lh->n at 88(a0) @+0x3a (buf->data+0) and lh->block[i] at
       92(a5) @+0x52 (buf->data+4+4i, a5 walking buf itself).
     Call sites (all four-byte [jal ra]):
       +0x24  jal initlock      (0x80000b88)  a0 = s2 = &log.lock (= &log),
                                              a1 = 0x800074f8 ("log")
       +0x36  jal bread         (0x80002b36)  a0 = s1 (dev),
                                              a1 = sb->logstart, STILL LIVE in
                                              a1 from the load at +0x28
                                              -> a0 = buf (kept in a0 throughout)
       +0x5e  jal brelse        (0x80002c3e)  a0 = buf (unchanged since bread)
       +0x64  jal install_trans (0x80003a8c)  a0 = 1  (recovering)
       +0x70  jal write_head    (0x80003a2e)  no arguments
     Loop (the [read_head] copy [log.lh.block[i] = lh->block[i]]):
       guard   +0x40  blez a2 -> +0x5e      (n <= 0: skip to brelse)
       setup   +0x44..+0x50 (a5 = buf, a4 = &log.lh.block[0], a2 = buf + 4*n)
       top     +0x52  (entered by FALLING THROUGH from +0x50 -- do-while shape)
       back    +0x5a  bne a5,a2 -> +0x52
       exit    +0x5e  (fall-through)
       induction: a5 (= buf + 4*i) against the end pointer a2; a4 walks
       &log.lh.block[i] in lock step (+0x56 / +0x58).
     Branch structure: exactly two branches (+0x40 and +0x5a), both above.
     No panic site, no early return.  Every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (20 words):
         0x7179, 0xf406, 0xf022, 0xec26, 0xe84a, 0xe44e, 0x1800, 0x84aa,
         0x89ae, 0x854a, 0x8526, 0x87aa, 0x4505, 0x70a2, 0x7402, 0x64e2,
         0x6942, 0x69a2, 0x6145, 0x8082
     * KernelBaseDecode.v (2 words):
         0x0001e717, 0x0001e797

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0x0001e917 -- also CodeVirtioDiskRw.v:rwb_0001e917
     0x00004597 -- also CodeIinit.v:iidb_00004597
   PROMOTED by the log.c decode-word dedup sweep.  Each word below was
   duplicated WITHIN the six log.c decode files and now lives once in
   KernelRvcDecode.v (compressed) / KernelBaseDecode.v (base), together with
   its leaf-shape expansion where that was duplicated too.  The local name is
   kept here as a RESTATEMENT with its original statement, closed by [exact]
   over the promoted lemma, so every consumer compiles untouched:
     0x00c05f63 (+ write_head), 0x060a (+ write_head, log_write),
     0x962a (+ write_head), 0x0791 (+ write_head),
     0x0711 (+ write_head, log_write), 0xfec79ce3 (+ write_head)
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
(* Compressed decode facts private to initlog.                    *)
(* ===================================================================== *)

(* 0x4d30  lw a2,88(a0) *)
Lemma ildc_4d30 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4d30 : mword 16)) s
  = Some (C_LW (mword_of_int 22, Cregidx (mword_of_int 2), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x060a  slli a2,a2,0x2 *)
Lemma ildc_060a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x060a : mword 16)) s
  = Some (C_SLLI (mword_of_int 2, Regidx (mword_of_int 12)), s).
Proof. exact (KernelRvcDecode.cdec_060a s). Qed.

(* 0x962a  add a2,a2,a0 *)
Lemma ildc_962a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x962a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 12), Regidx (mword_of_int 10)), s).
Proof. exact (KernelRvcDecode.cdec_962a s). Qed.

(* 0x4ff4  lw a3,92(a5) *)
Lemma ildc_4ff4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4ff4 : mword 16)) s
  = Some (C_LW (mword_of_int 23, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xc314  sw a3,0(a4) *)
Lemma ildc_c314 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc314 : mword 16)) s
  = Some (C_SW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0791  addi a5,a5,4 *)
Lemma ildc_0791 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0791 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 15)), s).
Proof. exact (KernelRvcDecode.cdec_0791 s). Qed.

(* 0x0711  addi a4,a4,4 *)
Lemma ildc_0711 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0711 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 14)), s).
Proof. exact (KernelRvcDecode.cdec_0711 s). Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma ilcx_4d30 s :
  exec (execute (C_LW (mword_of_int 22, Cregidx (mword_of_int 2), Cregidx (mword_of_int 4)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 88, Regidx (mword_of_int 10), Regidx (mword_of_int 12), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma ilcx_4ff4 s :
  exec (execute (C_LW (mword_of_int 23, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 92, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma ilcx_c314 s :
  exec (execute (C_SW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to initlog.                  *)
(* ===================================================================== *)

(* 0x0001e917  auipc s2,0x1e *)
Lemma ildb_0001e917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e917 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x7ae90913  addi s2,s2,1966 # 80022318 <log> *)
Lemma ildb_7ae90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7ae90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 1966 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x00004597  auipc a1,0x4 *)
Lemma ildb_00004597 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004597 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x98658593  addi a1,a1,-1658 # 800074f8 <etext+0x4f8> *)
Lemma ildb_98658593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x98658593 : mword 32)) s
  = Some (ITYPE (mword_of_int 2438 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x80cfd0ef  jal 80000b88 <initlock> *)
Lemma ildb_80cfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x80cfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084876 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0149a583  lw a1,20(s3) *)
Lemma ildb_0149a583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0149a583 : mword 32)) s
  = Some (LOAD (mword_of_int 20 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x00b92c23  sw a1,24(s2) *)
Lemma ildb_00b92c23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b92c23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x02992223  sw s1,36(s2) *)
Lemma ildb_02992223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02992223 : mword 32)) s
  = Some (STORE (mword_of_int 36 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xfa9fe0ef  jal 80002b36 <bread> *)
Lemma ildb_fa9fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa9fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092968 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x02c92623  sw a2,44(s2) *)
Lemma ildb_02c92623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02c92623 : mword 32)) s
  = Some (STORE (mword_of_int 44 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 18), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x00c05f63  blez a2,80003bb6 <initlog+0x5e> *)
Lemma ildb_00c05f63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c05f63 : mword 32)) s
  = Some (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE), s).
Proof. exact (KernelBaseDecode.bdec_00c05f63 s). Qed.

(* 0x7aa70713  addi a4,a4,1962 # 80022348 <log+0x30> *)
Lemma ildb_7aa70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7aa70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1962 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfec79ce3  bne a5,a2,80003baa <initlog+0x52> *)
Lemma ildb_fec79ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfec79ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE), s).
Proof. exact (KernelBaseDecode.bdec_fec79ce3 s). Qed.

(* 0x888ff0ef  jal 80002c3e <brelse> *)
Lemma ildb_888ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x888ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093192 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xed1ff0ef  jal 80003a8c <install_trans> *)
Lemma ildb_ed1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xed1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x7807a223  sw zero,1924(a5) # 80022344 <log+0x2c> *)
Lemma ildb_7807a223 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7807a223 : mword 32)) s
  = Some (STORE (mword_of_int 1924 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xe67ff0ef  jal 80003a2e <write_head> *)
Lemma ildb_e67ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe67ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096742 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InitlogInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* 0x00  7179  addi sp,sp,-48 *)
  Lemma ili_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  (* 0x02  f406  sd ra,40(sp) *)
  Lemma ili_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  (* 0x04  f022  sd s0,32(sp) *)
  Lemma ili_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  (* 0x06  ec26  sd s1,24(sp) *)
  Lemma ili_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  (* 0x08  e84a  sd s2,16(sp) *)
  Lemma ili_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  (* 0x0a  e44e  sd s3,8(sp) *)
  Lemma ili_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  (* 0x0c  1800  addi s0,sp,48 *)
  Lemma ili_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0e  84aa  mv s1,a0 *)
  Lemma ili_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x0e)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0x10  89ae  mv s3,a1 *)
  Lemma ili_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x10)%Z (mword_of_int 0x89ae : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)) cdec_89ae exec_execute_C_MV. Qed.

  (* 0x12  0001e917  auipc s2,0x1e *)
  Lemma ili_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x12) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KernelSyms.initlog + 0x12)%Z (mword_of_int 0x0001e917 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x12) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)) ildb_0001e917. Qed.

  (* 0x16  7ae90913  addi s2,s2,1966 # 80022318 <log> *)
  Lemma ili_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x16) : mword 64) false (ITYPE (mword_of_int 1966 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KernelSyms.initlog + 0x16)%Z (mword_of_int 0x7ae90913 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x16) : mword 64) (ITYPE (mword_of_int 1966 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) ildb_7ae90913. Qed.

  (* 0x1a  00004597  auipc a1,0x4 *)
  Lemma ili_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC)).
  Proof. mk_base (KernelSyms.initlog + 0x1a)%Z (mword_of_int 0x00004597 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x1a) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 11), AUIPC)) ildb_00004597. Qed.

  (* 0x1e  98658593  addi a1,a1,-1658 # 800074f8 <etext+0x4f8> *)
  Lemma ili_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x1e) : mword 64) false (ITYPE (mword_of_int 2438 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (KernelSyms.initlog + 0x1e)%Z (mword_of_int 0x98658593 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x1e) : mword 64) (ITYPE (mword_of_int 2438 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) ildb_98658593. Qed.

  (* 0x22  854a  mv a0,s2 *)
  Lemma ili_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x22)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  (* 0x24  80cfd0ef  jal 80000b88 <initlock> *)
  Lemma ili_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) false (JAL (mword_of_int 2084876 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.initlog + 0x24)%Z (mword_of_int 0x80cfd0ef : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x24) : mword 64) (JAL (mword_of_int 2084876 : mword 21, Regidx (mword_of_int 1))) ildb_80cfd0ef. Qed.

  (* 0x28  0149a583  lw a1,20(s3) *)
  Lemma ili_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x28) : mword 64) false (LOAD (mword_of_int 20 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (KernelSyms.initlog + 0x28)%Z (mword_of_int 0x0149a583 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x28) : mword 64) (LOAD (mword_of_int 20 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 11), false, 4)) ildb_0149a583. Qed.

  (* 0x2c  00b92c23  sw a1,24(s2) *)
  Lemma ili_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x2c) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (KernelSyms.initlog + 0x2c)%Z (mword_of_int 0x00b92c23 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x2c) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 11), Regidx (mword_of_int 18), 4)) ildb_00b92c23. Qed.

  (* 0x30  02992223  sw s1,36(s2) *)
  Lemma ili_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x30) : mword 64) false (STORE (mword_of_int 36 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (KernelSyms.initlog + 0x30)%Z (mword_of_int 0x02992223 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x30) : mword 64) (STORE (mword_of_int 36 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 18), 4)) ildb_02992223. Qed.

  (* 0x34  8526  mv a0,s1 *)
  Lemma ili_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x34) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x34)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x36  fa9fe0ef  jal 80002b36 <bread> *)
  Lemma ili_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) false (JAL (mword_of_int 2092968 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.initlog + 0x36)%Z (mword_of_int 0xfa9fe0ef : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x36) : mword 64) (JAL (mword_of_int 2092968 : mword 21, Regidx (mword_of_int 1))) ildb_fa9fe0ef. Qed.

  (* 0x3a  4d30  lw a2,88(a0) *)
  Lemma ili_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x3a) : mword 64) true (LOAD (mword_of_int 88, Regidx (mword_of_int 10), Regidx (mword_of_int 12), false, 4)).
  Proof. mk_rvc (KernelSyms.initlog + 0x3a)%Z (mword_of_int 0x4d30 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x3a) : mword 64) (LOAD (mword_of_int 88, Regidx (mword_of_int 10), Regidx (mword_of_int 12), false, 4)) ildc_4d30 ilcx_4d30. Qed.

  (* 0x3c  02c92623  sw a2,44(s2) *)
  Lemma ili_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x3c) : mword 64) false (STORE (mword_of_int 44 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (KernelSyms.initlog + 0x3c)%Z (mword_of_int 0x02c92623 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x3c) : mword 64) (STORE (mword_of_int 44 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 18), 4)) ildb_02c92623. Qed.

  (* 0x40  00c05f63  blez a2,80003bb6 <initlog+0x5e> *)
  Lemma ili_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x40) : mword 64) false (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (KernelSyms.initlog + 0x40)%Z (mword_of_int 0x00c05f63 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x40) : mword 64) (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)) ildb_00c05f63. Qed.

  (* 0x44  87aa  mv a5,a0 *)
  Lemma ili_44 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x44)%Z (mword_of_int 0x87aa : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) cdec_87aa exec_execute_C_MV. Qed.

  (* 0x46  0001e717  auipc a4,0x1e *)
  Lemma ili_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x46) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.initlog + 0x46)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x46) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  (* 0x4a  7aa70713  addi a4,a4,1962 # 80022348 <log+0x30> *)
  Lemma ili_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x4a) : mword 64) false (ITYPE (mword_of_int 1962 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.initlog + 0x4a)%Z (mword_of_int 0x7aa70713 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x4a) : mword 64) (ITYPE (mword_of_int 1962 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) ildb_7aa70713. Qed.

  (* 0x4e  060a  slli a2,a2,0x2 *)
  Lemma ili_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x4e) : mword 64) true (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x4e)%Z (mword_of_int 0x060a : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x4e) : mword 64) (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) ildc_060a exec_execute_C_SLLI. Qed.

  (* 0x50  962a  add a2,a2,a0 *)
  Lemma ili_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x50) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.initlog + 0x50)%Z (mword_of_int 0x962a : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)) ildc_962a exec_execute_C_ADD. Qed.

  (* 0x52  4ff4  lw a3,92(a5) *)
  Lemma ili_52 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x52) : mword 64) true (LOAD (mword_of_int 92, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 4)).
  Proof. mk_rvc (KernelSyms.initlog + 0x52)%Z (mword_of_int 0x4ff4 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x52) : mword 64) (LOAD (mword_of_int 92, Regidx (mword_of_int 15), Regidx (mword_of_int 13), false, 4)) ildc_4ff4 ilcx_4ff4. Qed.

  (* 0x54  c314  sw a3,0(a4) *)
  Lemma ili_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x54) : mword 64) true (STORE (mword_of_int 0, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (KernelSyms.initlog + 0x54)%Z (mword_of_int 0xc314 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x54) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)) ildc_c314 ilcx_c314. Qed.

  (* 0x56  0791  addi a5,a5,4 *)
  Lemma ili_56 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x56) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x56)%Z (mword_of_int 0x0791 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x56) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) ildc_0791 exec_execute_C_ADDI. Qed.

  (* 0x58  0711  addi a4,a4,4 *)
  Lemma ili_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x58) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x58)%Z (mword_of_int 0x0711 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x58) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) ildc_0711 exec_execute_C_ADDI. Qed.

  (* 0x5a  fec79ce3  bne a5,a2,80003baa <initlog+0x52> *)
  Lemma ili_5a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x5a) : mword 64) false (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.initlog + 0x5a)%Z (mword_of_int 0xfec79ce3 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x5a) : mword 64) (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE)) ildb_fec79ce3. Qed.

  (* 0x5e  888ff0ef  jal 80002c3e <brelse> *)
  Lemma ili_5e : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) false (JAL (mword_of_int 2093192 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.initlog + 0x5e)%Z (mword_of_int 0x888ff0ef : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x5e) : mword 64) (JAL (mword_of_int 2093192 : mword 21, Regidx (mword_of_int 1))) ildb_888ff0ef. Qed.

  (* 0x62  4505  li a0,1 *)
  Lemma ili_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x62) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x62)%Z (mword_of_int 0x4505 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x62) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4505 exec_execute_C_LI. Qed.

  (* 0x64  ed1ff0ef  jal 80003a8c <install_trans> *)
  Lemma ili_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) false (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.initlog + 0x64)%Z (mword_of_int 0xed1ff0ef : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x64) : mword 64) (JAL (mword_of_int 2096848 : mword 21, Regidx (mword_of_int 1))) ildb_ed1ff0ef. Qed.

  (* 0x68  0001e797  auipc a5,0x1e *)
  Lemma ili_68 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x68) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.initlog + 0x68)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x68) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x6c  7807a223  sw zero,1924(a5) # 80022344 <log+0x2c> *)
  Lemma ili_6c : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x6c) : mword 64) false (STORE (mword_of_int 1924 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (KernelSyms.initlog + 0x6c)%Z (mword_of_int 0x7807a223 : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x6c) : mword 64) (STORE (mword_of_int 1924 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 4)) ildb_7807a223. Qed.

  (* 0x70  e67ff0ef  jal 80003a2e <write_head> *)
  Lemma ili_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) false (JAL (mword_of_int 2096742 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.initlog + 0x70)%Z (mword_of_int 0xe67ff0ef : mword 32)
    (mword_of_int (KernelSyms.initlog + 0x70) : mword 64) (JAL (mword_of_int 2096742 : mword 21, Regidx (mword_of_int 1))) ildb_e67ff0ef. Qed.

  (* 0x74  70a2  ld ra,40(sp) *)
  Lemma ili_74 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x74) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x74)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x74) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  (* 0x76  7402  ld s0,32(sp) *)
  Lemma ili_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x76)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  (* 0x78  64e2  ld s1,24(sp) *)
  Lemma ili_78 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x78)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  (* 0x7a  6942  ld s2,16(sp) *)
  Lemma ili_7a : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x7a)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  (* 0x7c  69a2  ld s3,8(sp) *)
  Lemma ili_7c : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.initlog + 0x7c)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  (* 0x7e  6145  addi sp,sp,48 *)
  Lemma ili_7e : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x7e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.initlog + 0x7e)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x7e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  (* 0x80  8082  ret *)
  Lemma ili_80 : kernel_text -∗ instr (mword_of_int (KernelSyms.initlog + 0x80) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.initlog + 0x80)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.initlog + 0x80) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End InitlogInstrs.

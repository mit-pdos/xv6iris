(* CodeWriteHead.v -- the instruction-DECODE layer for xv6's write_head().
   For EVERY instruction of

     write_head @ 0x80003a2e .. 0x80003a8a   (offsets 0x00 .. 0x5c, 94 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([whi_<off>]) plus
   the per-instruction decode facts they consume ([whdc_<word>] compressed /
   [whdb_<word>] base / [whcx_<word>] the compressed leaf expansions).
   write_head is [static]; its callers are initlog (via recover_from_log) and
   end_op (via commit).

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

     0x00 1101     addi sp,sp,-32
     0x02 ec06     sd ra,24(sp)
     0x04 e822     sd s0,16(sp)
     0x06 e426     sd s1,8(sp)
     0x08 e04a     sd s2,0(sp)
     0x0a 1000     addi s0,sp,32
     0x0c 0001f917 auipc s2,0x1f
     0x10 8de90913 addi s2,s2,-1826 # 80022318 <log>
     0x14 01892583 lw a1,24(s2)
     0x18 02492503 lw a0,36(s2)
     0x1c 8ecff0ef jal 80002b36 <bread>
     0x20 84aa     mv s1,a0
     0x22 02c92603 lw a2,44(s2)
     0x26 cd30     sw a2,88(a0)
     0x28 00c05f63 blez a2,80003a74 <write_head+0x46>
     0x2c 0001f717 auipc a4,0x1f
     0x30 8ee70713 addi a4,a4,-1810 # 80022348 <log+0x30>
     0x34 87aa     mv a5,a0
     0x36 060a     slli a2,a2,0x2
     0x38 962a     add a2,a2,a0
     0x3a 4314     lw a3,0(a4)
     0x3c cff4     sw a3,92(a5)
     0x3e 0711     addi a4,a4,4
     0x40 0791     addi a5,a5,4
     0x42 fec79ce3 bne a5,a2,80003a68 <write_head+0x3a>
     0x46 8526     mv a0,s1
     0x48 996ff0ef jal 80002c0c <bwrite>
     0x4c 8526     mv a0,s1
     0x4e 9c2ff0ef jal 80002c3e <brelse>
     0x52 60e2     ld ra,24(sp)
     0x54 6442     ld s0,16(sp)
     0x56 64a2     ld s1,8(sp)
     0x58 6902     ld s2,0(sp)
     0x5a 6105     addi sp,sp,32
     0x5c 8082     ret

   STRUCTURE.
     Frame: 32 bytes ([c.addi sp,sp,-32] at +0x00, [c.addi16sp sp,32] at +0x5a).
       Saved: ra@24(sp), s0@16(sp), s1@8(sp), s2@0(sp); s0 = sp+32 (frame ptr).
     Register roles: s2 = &log (0x80022318); s1 = the header buffer returned by
       bread; a5 = the destination cursor into buf (buf + 4*i); a4 = the source
       cursor &log.lh.block[i]; a2 = first log.lh.n, then the end sentinel
       buf + 4*n; a3 = the word in flight.
     Log fields touched: READS log.start(+24) @+0x14, log.dev(+36) @+0x18,
       log.lh.n(+44) @+0x22, log.lh.block[i](+48+4i) @+0x3a.  WRITES none --
       write_head only copies the in-memory header OUT to the buffer.
     Buffer fields touched: hb->n at 88(a0) @+0x26 (that is buf->data+0), and
       hb->block[i] at 92(a5) @+0x3c (buf->data+4+4i, since a5 walks buf itself).
     Call sites (all four-byte [jal ra]):
       +0x1c  jal bread     (0x80002b36)  a0 = log.dev, a1 = log.start
                                          -> a0 = buf, parked in s1 at +0x20
       +0x48  jal bwrite    (0x80002c0c)  a0 = s1 (buf)
       +0x4e  jal brelse    (0x80002c3e)  a0 = s1 (buf)
     Loop (the [for (i = 0; i < log.lh.n; i++)] header copy):
       guard   +0x28  blez a2 -> +0x46      (n <= 0: skip the loop entirely)
       setup   +0x2c..+0x38 (a4 = &log.lh.block[0], a5 = buf, a2 = buf + 4*n)
       top     +0x3a  (entered by FALLING THROUGH from +0x38 -- do-while shape)
       back    +0x42  bne a5,a2 -> +0x3a
       exit    +0x46  (fall-through)
       induction: a5 (= buf + 4*i) against the end pointer a2; a4 and a5 are
       bumped in lock step at +0x3e / +0x40, so i is only implicit.
     Branch structure: exactly two branches, both listed above; no other
       conditional control flow, no panic site, no early return.
     Every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (15 words):
         0x1101, 0xec06, 0xe822, 0xe426, 0xe04a, 0x1000, 0x84aa, 0x87aa,
         0x8526, 0x60e2, 0x6442, 0x64a2, 0x6902, 0x6105, 0x8082

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0x0001f717 -- also CodeFilealloc.v:fadb_0001f717
   Also duplicated WITHIN the six new log.c decode files (same argument --
   these are the strongest promotion candidates):
     0x00c05f63 (+ initlog), 0x060a (+ initlog, log_write),
     0x962a (+ initlog), 0x4314 (+ log_write),
     0x0711 (+ initlog, log_write), 0x0791 (+ initlog),
     0xfec79ce3 (+ initlog)
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
(* Compressed decode facts private to write_head.                    *)
(* ===================================================================== *)

(* 0xcd30  sw a2,88(a0) *)
Lemma whdc_cd30 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd30 : mword 16)) s
  = Some (C_SW (mword_of_int 22, Cregidx (mword_of_int 2), Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x060a  slli a2,a2,0x2 *)
Lemma whdc_060a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x060a : mword 16)) s
  = Some (C_SLLI (mword_of_int 2, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x962a  add a2,a2,a0 *)
Lemma whdc_962a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x962a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 12), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4314  lw a3,0(a4) *)
Lemma whdc_4314 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4314 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcff4  sw a3,92(a5) *)
Lemma whdc_cff4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcff4 : mword 16)) s
  = Some (C_SW (mword_of_int 23, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0711  addi a4,a4,4 *)
Lemma whdc_0711 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0711 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0791  addi a5,a5,4 *)
Lemma whdc_0791 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0791 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma whcx_cd30 s :
  exec (execute (C_SW (mword_of_int 22, Cregidx (mword_of_int 2), Cregidx (mword_of_int 4)))) s
  = Some (ExecuteAs (STORE (mword_of_int 88, Regidx (mword_of_int 12), Regidx (mword_of_int 10), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma whcx_4314 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma whcx_cff4 s :
  exec (execute (C_SW (mword_of_int 23, Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (STORE (mword_of_int 92, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to write_head.                  *)
(* ===================================================================== *)

(* 0x0001f917  auipc s2,0x1f *)
Lemma whdb_0001f917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001f917 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x8de90913  addi s2,s2,-1826 # 80022318 <log> *)
Lemma whdb_8de90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8de90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 2270 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x01892583  lw a1,24(s2) *)
Lemma whdb_01892583 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01892583 : mword 32)) s
  = Some (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x02492503  lw a0,36(s2) *)
Lemma whdb_02492503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02492503 : mword 32)) s
  = Some (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x8ecff0ef  jal 80002b36 <bread> *)
Lemma whdb_8ecff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8ecff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093292 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x02c92603  lw a2,44(s2) *)
Lemma whdb_02c92603 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02c92603 : mword 32)) s
  = Some (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x00c05f63  blez a2,80003a74 <write_head+0x46> *)
Lemma whdb_00c05f63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c05f63 : mword 32)) s
  = Some (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001f717  auipc a4,0x1f *)
Lemma whdb_0001f717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001f717 : mword 32)) s
  = Some (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x8ee70713  addi a4,a4,-1810 # 80022348 <log+0x30> *)
Lemma whdb_8ee70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8ee70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 2286 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfec79ce3  bne a5,a2,80003a68 <write_head+0x3a> *)
Lemma whdb_fec79ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfec79ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0x996ff0ef  jal 80002c0c <bwrite> *)
Lemma whdb_996ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x996ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093462 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x9c2ff0ef  jal 80002c3e <brelse> *)
Lemma whdb_9c2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9c2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093506 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section WriteHeadInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation WH := KernelSyms.write_head.

  (* 0x00  1101  addi sp,sp,-32 *)
  Lemma whi_00 : kernel_text -∗ instr (mword_of_int (WH + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (WH + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (WH + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  (* 0x02  ec06  sd ra,24(sp) *)
  Lemma whi_02 : kernel_text -∗ instr (mword_of_int (WH + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (WH + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (WH + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  (* 0x04  e822  sd s0,16(sp) *)
  Lemma whi_04 : kernel_text -∗ instr (mword_of_int (WH + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (WH + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (WH + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  (* 0x06  e426  sd s1,8(sp) *)
  Lemma whi_06 : kernel_text -∗ instr (mword_of_int (WH + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (WH + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (WH + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  (* 0x08  e04a  sd s2,0(sp) *)
  Lemma whi_08 : kernel_text -∗ instr (mword_of_int (WH + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (WH + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (WH + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  (* 0x0a  1000  addi s0,sp,32 *)
  Lemma whi_0a : kernel_text -∗ instr (mword_of_int (WH + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (WH + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (WH + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0c  0001f917  auipc s2,0x1f *)
  Lemma whi_0c : kernel_text -∗ instr (mword_of_int (WH + 0x0c) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (WH + 0x0c)%Z (mword_of_int 0x0001f917 : mword 32)
    (mword_of_int (WH + 0x0c) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 18), AUIPC)) whdb_0001f917. Qed.

  (* 0x10  8de90913  addi s2,s2,-1826 # 80022318 <log> *)
  Lemma whi_10 : kernel_text -∗ instr (mword_of_int (WH + 0x10) : mword 64) false (ITYPE (mword_of_int 2270 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (WH + 0x10)%Z (mword_of_int 0x8de90913 : mword 32)
    (mword_of_int (WH + 0x10) : mword 64) (ITYPE (mword_of_int 2270 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) whdb_8de90913. Qed.

  (* 0x14  01892583  lw a1,24(s2) *)
  Lemma whi_14 : kernel_text -∗ instr (mword_of_int (WH + 0x14) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_base (WH + 0x14)%Z (mword_of_int 0x01892583 : mword 32)
    (mword_of_int (WH + 0x14) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 11), false, 4)) whdb_01892583. Qed.

  (* 0x18  02492503  lw a0,36(s2) *)
  Lemma whi_18 : kernel_text -∗ instr (mword_of_int (WH + 0x18) : mword 64) false (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)).
  Proof. mk_base (WH + 0x18)%Z (mword_of_int 0x02492503 : mword 32)
    (mword_of_int (WH + 0x18) : mword 64) (LOAD (mword_of_int 36 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 10), false, 4)) whdb_02492503. Qed.

  (* 0x1c  8ecff0ef  jal 80002b36 <bread> *)
  Lemma whi_1c : kernel_text -∗ instr (mword_of_int (WH + 0x1c) : mword 64) false (JAL (mword_of_int 2093292 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WH + 0x1c)%Z (mword_of_int 0x8ecff0ef : mword 32)
    (mword_of_int (WH + 0x1c) : mword 64) (JAL (mword_of_int 2093292 : mword 21, Regidx (mword_of_int 1))) whdb_8ecff0ef. Qed.

  (* 0x20  84aa  mv s1,a0 *)
  Lemma whi_20 : kernel_text -∗ instr (mword_of_int (WH + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (WH + 0x20)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (WH + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0x22  02c92603  lw a2,44(s2) *)
  Lemma whi_22 : kernel_text -∗ instr (mword_of_int (WH + 0x22) : mword 64) false (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12), false, 4)).
  Proof. mk_base (WH + 0x22)%Z (mword_of_int 0x02c92603 : mword 32)
    (mword_of_int (WH + 0x22) : mword 64) (LOAD (mword_of_int 44 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12), false, 4)) whdb_02c92603. Qed.

  (* 0x26  cd30  sw a2,88(a0) *)
  Lemma whi_26 : kernel_text -∗ instr (mword_of_int (WH + 0x26) : mword 64) true (STORE (mword_of_int 88, Regidx (mword_of_int 12), Regidx (mword_of_int 10), 4)).
  Proof. mk_rvc (WH + 0x26)%Z (mword_of_int 0xcd30 : mword 16)
    (mword_of_int (WH + 0x26) : mword 64) (STORE (mword_of_int 88, Regidx (mword_of_int 12), Regidx (mword_of_int 10), 4)) whdc_cd30 whcx_cd30. Qed.

  (* 0x28  00c05f63  blez a2,80003a74 <write_head+0x46> *)
  Lemma whi_28 : kernel_text -∗ instr (mword_of_int (WH + 0x28) : mword 64) false (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (WH + 0x28)%Z (mword_of_int 0x00c05f63 : mword 32)
    (mword_of_int (WH + 0x28) : mword 64) (BTYPE (mword_of_int 30 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)) whdb_00c05f63. Qed.

  (* 0x2c  0001f717  auipc a4,0x1f *)
  Lemma whi_2c : kernel_text -∗ instr (mword_of_int (WH + 0x2c) : mword 64) false (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (WH + 0x2c)%Z (mword_of_int 0x0001f717 : mword 32)
    (mword_of_int (WH + 0x2c) : mword 64) (UTYPE (mword_of_int 31 : mword 20, Regidx (mword_of_int 14), AUIPC)) whdb_0001f717. Qed.

  (* 0x30  8ee70713  addi a4,a4,-1810 # 80022348 <log+0x30> *)
  Lemma whi_30 : kernel_text -∗ instr (mword_of_int (WH + 0x30) : mword 64) false (ITYPE (mword_of_int 2286 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (WH + 0x30)%Z (mword_of_int 0x8ee70713 : mword 32)
    (mword_of_int (WH + 0x30) : mword 64) (ITYPE (mword_of_int 2286 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) whdb_8ee70713. Qed.

  (* 0x34  87aa  mv a5,a0 *)
  Lemma whi_34 : kernel_text -∗ instr (mword_of_int (WH + 0x34) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (WH + 0x34)%Z (mword_of_int 0x87aa : mword 16)
    (mword_of_int (WH + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 15), ADD)) cdec_87aa exec_execute_C_MV. Qed.

  (* 0x36  060a  slli a2,a2,0x2 *)
  Lemma whi_36 : kernel_text -∗ instr (mword_of_int (WH + 0x36) : mword 64) true (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (WH + 0x36)%Z (mword_of_int 0x060a : mword 16)
    (mword_of_int (WH + 0x36) : mword 64) (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) whdc_060a exec_execute_C_SLLI. Qed.

  (* 0x38  962a  add a2,a2,a0 *)
  Lemma whi_38 : kernel_text -∗ instr (mword_of_int (WH + 0x38) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (WH + 0x38)%Z (mword_of_int 0x962a : mword 16)
    (mword_of_int (WH + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADD)) whdc_962a exec_execute_C_ADD. Qed.

  (* 0x3a  4314  lw a3,0(a4) *)
  Lemma whi_3a : kernel_text -∗ instr (mword_of_int (WH + 0x3a) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)).
  Proof. mk_rvc (WH + 0x3a)%Z (mword_of_int 0x4314 : mword 16)
    (mword_of_int (WH + 0x3a) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)) whdc_4314 whcx_4314. Qed.

  (* 0x3c  cff4  sw a3,92(a5) *)
  Lemma whi_3c : kernel_text -∗ instr (mword_of_int (WH + 0x3c) : mword 64) true (STORE (mword_of_int 92, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (WH + 0x3c)%Z (mword_of_int 0xcff4 : mword 16)
    (mword_of_int (WH + 0x3c) : mword 64) (STORE (mword_of_int 92, Regidx (mword_of_int 13), Regidx (mword_of_int 15), 4)) whdc_cff4 whcx_cff4. Qed.

  (* 0x3e  0711  addi a4,a4,4 *)
  Lemma whi_3e : kernel_text -∗ instr (mword_of_int (WH + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (WH + 0x3e)%Z (mword_of_int 0x0711 : mword 16)
    (mword_of_int (WH + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) whdc_0711 exec_execute_C_ADDI. Qed.

  (* 0x40  0791  addi a5,a5,4 *)
  Lemma whi_40 : kernel_text -∗ instr (mword_of_int (WH + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (WH + 0x40)%Z (mword_of_int 0x0791 : mword 16)
    (mword_of_int (WH + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) whdc_0791 exec_execute_C_ADDI. Qed.

  (* 0x42  fec79ce3  bne a5,a2,80003a68 <write_head+0x3a> *)
  Lemma whi_42 : kernel_text -∗ instr (mword_of_int (WH + 0x42) : mword 64) false (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (WH + 0x42)%Z (mword_of_int 0xfec79ce3 : mword 32)
    (mword_of_int (WH + 0x42) : mword 64) (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BNE)) whdb_fec79ce3. Qed.

  (* 0x46  8526  mv a0,s1 *)
  Lemma whi_46 : kernel_text -∗ instr (mword_of_int (WH + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WH + 0x46)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (WH + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x48  996ff0ef  jal 80002c0c <bwrite> *)
  Lemma whi_48 : kernel_text -∗ instr (mword_of_int (WH + 0x48) : mword 64) false (JAL (mword_of_int 2093462 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WH + 0x48)%Z (mword_of_int 0x996ff0ef : mword 32)
    (mword_of_int (WH + 0x48) : mword 64) (JAL (mword_of_int 2093462 : mword 21, Regidx (mword_of_int 1))) whdb_996ff0ef. Qed.

  (* 0x4c  8526  mv a0,s1 *)
  Lemma whi_4c : kernel_text -∗ instr (mword_of_int (WH + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (WH + 0x4c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (WH + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x4e  9c2ff0ef  jal 80002c3e <brelse> *)
  Lemma whi_4e : kernel_text -∗ instr (mword_of_int (WH + 0x4e) : mword 64) false (JAL (mword_of_int 2093506 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (WH + 0x4e)%Z (mword_of_int 0x9c2ff0ef : mword 32)
    (mword_of_int (WH + 0x4e) : mword 64) (JAL (mword_of_int 2093506 : mword 21, Regidx (mword_of_int 1))) whdb_9c2ff0ef. Qed.

  (* 0x52  60e2  ld ra,24(sp) *)
  Lemma whi_52 : kernel_text -∗ instr (mword_of_int (WH + 0x52) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (WH + 0x52)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (WH + 0x52) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  (* 0x54  6442  ld s0,16(sp) *)
  Lemma whi_54 : kernel_text -∗ instr (mword_of_int (WH + 0x54) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (WH + 0x54)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (WH + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  (* 0x56  64a2  ld s1,8(sp) *)
  Lemma whi_56 : kernel_text -∗ instr (mword_of_int (WH + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (WH + 0x56)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (WH + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* 0x58  6902  ld s2,0(sp) *)
  Lemma whi_58 : kernel_text -∗ instr (mword_of_int (WH + 0x58) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (WH + 0x58)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (WH + 0x58) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  (* 0x5a  6105  addi sp,sp,32 *)
  Lemma whi_5a : kernel_text -∗ instr (mword_of_int (WH + 0x5a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (WH + 0x5a)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (WH + 0x5a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* 0x5c  8082  ret *)
  Lemma whi_5c : kernel_text -∗ instr (mword_of_int (WH + 0x5c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (WH + 0x5c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (WH + 0x5c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WriteHeadInstrs.

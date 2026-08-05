(* CodeBeginOp.v -- the instruction-DECODE layer for xv6's begin_op().
   For EVERY instruction of

     begin_op @ 0x80003bda .. 0x80003c48   (offsets 0x00 .. 0x6e, 112 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([boi_<off>]) plus
   the per-instruction decode facts they consume ([bodc_<word>] compressed /
   [bodb_<word>] base / [bocx_<word>] the compressed leaf expansions).

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
     0x0c 0001e517 auipc a0,0x1e
     0x10 73250513 addi a0,a0,1842 # 80022318 <log>
     0x14 81afd0ef jal 80000c08 <acquire>
     0x18 0001e497 auipc s1,0x1e
     0x1c 72648493 addi s1,s1,1830 # 80022318 <log>
     0x20 4979     li s2,30
     0x22 a029     j 80003c06 <begin_op+0x2c>
     0x24 85a6     mv a1,s1
     0x26 8526     mv a0,s1
     0x28 b04fe0ef jal 80001f06 <sleep>
     0x2c 509c     lw a5,32(s1)
     0x2e fbfd     bnez a5,80003bfe <begin_op+0x24>
     0x30 4cd8     lw a4,28(s1)
     0x32 2705     addiw a4,a4,1
     0x34 0027179b slliw a5,a4,0x2
     0x38 9fb9     addw a5,a5,a4
     0x3a 0017979b slliw a5,a5,0x1
     0x3e 54d4     lw a3,44(s1)
     0x40 9fb5     addw a5,a5,a3
     0x42 00f95763 bge s2,a5,80003c2a <begin_op+0x50>
     0x46 85a6     mv a1,s1
     0x48 8526     mv a0,s1
     0x4a ae2fe0ef jal 80001f06 <sleep>
     0x4e bff9     j 80003c06 <begin_op+0x2c>
     0x50 0001e797 auipc a5,0x1e
     0x54 70e7a523 sw a4,1802(a5) # 80022334 <log+0x1c>
     0x58 0001e517 auipc a0,0x1e
     0x5c 6e650513 addi a0,a0,1766 # 80022318 <log>
     0x60 856fd0ef jal 80000c90 <release>
     0x64 60e2     ld ra,24(sp)
     0x66 6442     ld s0,16(sp)
     0x68 64a2     ld s1,8(sp)
     0x6a 6902     ld s2,0(sp)
     0x6c 6105     addi sp,sp,32
     0x6e 8082     ret

   STRUCTURE.
     Frame: 32 bytes ([c.addi sp,sp,-32] at +0x00, [c.addi16sp sp,32] at +0x6c).
       Saved: ra@24, s0@16, s1@8, s2@0; s0 = sp+32.
     Register roles: s1 = &log (0x80022318), reloaded at +0x18 after the
       acquire call; s2 = 30 = LOGBLOCKS, the space bound, materialised once at
       +0x20; a4 = log.outstanding then outstanding+1 (the value written back);
       a5 = the scratch that carries log.committing and then the size estimate
       MAXOPBLOCKS*(outstanding+1) + log.lh.n; a3 = log.lh.n.
     Log fields touched: READS log.committing(+32) @+0x2c,
       log.outstanding(+28) @+0x30, log.lh.n(+44) @+0x3e.
       WRITES log.outstanding(+28) @+0x54 (the auipc/sw pair at +0x50/+0x54
       targets 0x80022334 directly, NOT through s1).
     Call sites (all four-byte [jal ra]):
       +0x14  jal acquire (0x80000c08)  a0 = &log.lock (= &log = 0x80022318)
       +0x28  jal sleep   (0x80001f06)  a0 = s1 (chan = &log), a1 = s1 (lk =
                                        &log.lock) -- the COMMITTING arm
       +0x4a  jal sleep   (0x80001f06)  a0 = s1, a1 = s1 -- the NO-SPACE arm
       +0x60  jal release (0x80000c90)  a0 = &log.lock (= &log)
     Loop (the C's [while (1)] retry): this is a CONDITION loop with no
       induction variable; each iteration re-reads log.committing and
       log.lh.n / log.outstanding under the lock that sleep re-acquires.
       entry   +0x22  j -> +0x2c    (jump straight to the test)
       test    +0x2c  lw a5,32(s1)  (log.committing)
       arm A   +0x2e  bnez a5 -> +0x24 ; the block +0x24..+0x2a ends at the
               sleep call and FALLS THROUGH back into the test at +0x2c
       arm B   +0x42  bge s2,a5 NOT taken -> fall into +0x46..+0x4c (sleep),
               then +0x4e  j -> +0x2c
       exit    +0x42  bge s2,a5 taken -> +0x50 (the [outstanding += 1] tail)
       So the loop's back edges are (+0x2a fall-through) and (+0x4e j), and its
       single exit is the +0x42 branch.
     The size test, spelled out (+0x30..+0x42):
       a4 = log.outstanding ; a4 = a4+1 ; a5 = a4<<2 ; a5 = a5+a4 (= 5*a4) ;
       a5 = a5<<1 (= 10*a4 = MAXOPBLOCKS*(outstanding+1)) ; a3 = log.lh.n ;
       a5 = a5+a3 ; branch if 30 >= a5.  All four of slliw/addw/slliw/addw are
       W-form, so the estimate is computed in 32 bits and sign-extended.
     Branch structure: +0x22 (j to test), +0x2e (bnez committing -> sleep arm),
       +0x42 (bge: the only exit), +0x4e (j back to test).
     No panic site.  Every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (16 words):
         0x1101, 0xec06, 0xe822, 0xe426, 0xe04a, 0x1000, 0x85a6, 0x8526,
         0xfbfd, 0xbff9, 0x60e2, 0x6442, 0x64a2, 0x6902, 0x6105, 0x8082
     * KernelBaseDecode.v (3 words):
         0x0001e517, 0x0001e497, 0x0001e797

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0xa029 -- also CodePipealloc.v:padc_a029
     0x9fb9 -- also CodeProcinit.v:pidc_9fb9
   Also duplicated WITHIN the six new log.c decode files (same argument --
   these are the strongest promotion candidates):
     0x509c (+ end_op)
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
(* Compressed decode facts private to begin_op.                    *)
(* ===================================================================== *)

(* 0x4979  li s2,30 *)
Lemma bodc_4979 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4979 : mword 16)) s
  = Some (C_LI (mword_of_int 30, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa029  j 80003c06 <begin_op+0x2c> *)
Lemma bodc_a029 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa029 : mword 16)) s
  = Some (C_J (mword_of_int 5), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x509c  lw a5,32(s1) *)
Lemma bodc_509c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x509c : mword 16)) s
  = Some (C_LW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4cd8  lw a4,28(s1) *)
Lemma bodc_4cd8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4cd8 : mword 16)) s
  = Some (C_LW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2705  addiw a4,a4,1 *)
Lemma bodc_2705 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2705 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9fb9  addw a5,a5,a4 *)
Lemma bodc_9fb9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9fb9 : mword 16)) s
  = Some (C_ADDW (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x54d4  lw a3,44(s1) *)
Lemma bodc_54d4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x54d4 : mword 16)) s
  = Some (C_LW (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x9fb5  addw a5,a5,a3 *)
Lemma bodc_9fb5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9fb5 : mword 16)) s
  = Some (C_ADDW (Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma bocx_509c s :
  exec (execute (C_LW (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bocx_4cd8 s :
  exec (execute (C_LW (mword_of_int 7, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bocx_54d4 s :
  exec (execute (C_LW (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to begin_op.                  *)
(* ===================================================================== *)

(* 0x73250513  addi a0,a0,1842 # 80022318 <log> *)
Lemma bodb_73250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x73250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1842 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x81afd0ef  jal 80000c08 <acquire> *)
Lemma bodb_81afd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81afd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084890 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x72648493  addi s1,s1,1830 # 80022318 <log> *)
Lemma bodb_72648493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x72648493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1830 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xb04fe0ef  jal 80001f06 <sleep> *)
Lemma bodb_b04fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb04fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089732 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0027179b  slliw a5,a4,0x2 *)
Lemma bodb_0027179b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0027179b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 2 : mword 5, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* 0x0017979b  slliw a5,a5,0x1 *)
Lemma bodb_0017979b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017979b : mword 32)) s
  = Some (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLIW), s).
Proof. decode_bridge_ms. Qed.

(* 0x00f95763  bge s2,a5,80003c2a <begin_op+0x50> *)
Lemma bodb_00f95763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f95763 : mword 32)) s
  = Some (BTYPE (mword_of_int 14 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0xae2fe0ef  jal 80001f06 <sleep> *)
Lemma bodb_ae2fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xae2fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089698 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x70e7a523  sw a4,1802(a5) # 80022334 <log+0x1c> *)
Lemma bodb_70e7a523 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x70e7a523 : mword 32)) s
  = Some (STORE (mword_of_int 1802 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x6e650513  addi a0,a0,1766 # 80022318 <log> *)
Lemma bodb_6e650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x6e650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1766 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x856fd0ef  jal 80000c90 <release> *)
Lemma bodb_856fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x856fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084950 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BeginOpInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation BO := KernelSyms.begin_op.

  (* 0x00  1101  addi sp,sp,-32 *)
  Lemma boi_00 : kernel_text -∗ instr (mword_of_int (BO + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (BO + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (BO + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  (* 0x02  ec06  sd ra,24(sp) *)
  Lemma boi_02 : kernel_text -∗ instr (mword_of_int (BO + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BO + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (BO + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  (* 0x04  e822  sd s0,16(sp) *)
  Lemma boi_04 : kernel_text -∗ instr (mword_of_int (BO + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BO + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (BO + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  (* 0x06  e426  sd s1,8(sp) *)
  Lemma boi_06 : kernel_text -∗ instr (mword_of_int (BO + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BO + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (BO + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  (* 0x08  e04a  sd s2,0(sp) *)
  Lemma boi_08 : kernel_text -∗ instr (mword_of_int (BO + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (BO + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (BO + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  (* 0x0a  1000  addi s0,sp,32 *)
  Lemma boi_0a : kernel_text -∗ instr (mword_of_int (BO + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BO + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (BO + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0c  0001e517  auipc a0,0x1e *)
  Lemma boi_0c : kernel_text -∗ instr (mword_of_int (BO + 0x0c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BO + 0x0c)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (BO + 0x0c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x10  73250513  addi a0,a0,1842 # 80022318 <log> *)
  Lemma boi_10 : kernel_text -∗ instr (mword_of_int (BO + 0x10) : mword 64) false (ITYPE (mword_of_int 1842 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BO + 0x10)%Z (mword_of_int 0x73250513 : mword 32)
    (mword_of_int (BO + 0x10) : mword 64) (ITYPE (mword_of_int 1842 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bodb_73250513. Qed.

  (* 0x14  81afd0ef  jal 80000c08 <acquire> *)
  Lemma boi_14 : kernel_text -∗ instr (mword_of_int (BO + 0x14) : mword 64) false (JAL (mword_of_int 2084890 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BO + 0x14)%Z (mword_of_int 0x81afd0ef : mword 32)
    (mword_of_int (BO + 0x14) : mword 64) (JAL (mword_of_int 2084890 : mword 21, Regidx (mword_of_int 1))) bodb_81afd0ef. Qed.

  (* 0x18  0001e497  auipc s1,0x1e *)
  Lemma boi_18 : kernel_text -∗ instr (mword_of_int (BO + 0x18) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (BO + 0x18)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (BO + 0x18) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  (* 0x1c  72648493  addi s1,s1,1830 # 80022318 <log> *)
  Lemma boi_1c : kernel_text -∗ instr (mword_of_int (BO + 0x1c) : mword 64) false (ITYPE (mword_of_int 1830 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (BO + 0x1c)%Z (mword_of_int 0x72648493 : mword 32)
    (mword_of_int (BO + 0x1c) : mword 64) (ITYPE (mword_of_int 1830 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bodb_72648493. Qed.

  (* 0x20  4979  li s2,30 *)
  Lemma boi_20 : kernel_text -∗ instr (mword_of_int (BO + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 30 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (BO + 0x20)%Z (mword_of_int 0x4979 : mword 16)
    (mword_of_int (BO + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 30 : mword 6), zreg, Regidx (mword_of_int 18), ADDI)) bodc_4979 exec_execute_C_LI. Qed.

  (* 0x22  a029  j 80003c06 <begin_op+0x2c> *)
  Lemma boi_22 : kernel_text -∗ instr (mword_of_int (BO + 0x22) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BO + 0x22)%Z (mword_of_int 0xa029 : mword 16)
    (mword_of_int (BO + 0x22) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 5 : mword 11) ('b"0")), zreg)) bodc_a029 exec_execute_C_J. Qed.

  (* 0x24  85a6  mv a1,s1 *)
  Lemma boi_24 : kernel_text -∗ instr (mword_of_int (BO + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (BO + 0x24)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (BO + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* 0x26  8526  mv a0,s1 *)
  Lemma boi_26 : kernel_text -∗ instr (mword_of_int (BO + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BO + 0x26)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (BO + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x28  b04fe0ef  jal 80001f06 <sleep> *)
  Lemma boi_28 : kernel_text -∗ instr (mword_of_int (BO + 0x28) : mword 64) false (JAL (mword_of_int 2089732 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BO + 0x28)%Z (mword_of_int 0xb04fe0ef : mword 32)
    (mword_of_int (BO + 0x28) : mword 64) (JAL (mword_of_int 2089732 : mword 21, Regidx (mword_of_int 1))) bodb_b04fe0ef. Qed.

  (* 0x2c  509c  lw a5,32(s1) *)
  Lemma boi_2c : kernel_text -∗ instr (mword_of_int (BO + 0x2c) : mword 64) true (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BO + 0x2c)%Z (mword_of_int 0x509c : mword 16)
    (mword_of_int (BO + 0x2c) : mword 64) (LOAD (mword_of_int 32, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bodc_509c bocx_509c. Qed.

  (* 0x2e  fbfd  bnez a5,80003bfe <begin_op+0x24> *)
  Lemma boi_2e : kernel_text -∗ instr (mword_of_int (BO + 0x2e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (BO + 0x2e)%Z (mword_of_int 0xfbfd : mword 16)
    (mword_of_int (BO + 0x2e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 251 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) cdec_fbfd exec_execute_C_BNEZ. Qed.

  (* 0x30  4cd8  lw a4,28(s1) *)
  Lemma boi_30 : kernel_text -∗ instr (mword_of_int (BO + 0x30) : mword 64) true (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (BO + 0x30)%Z (mword_of_int 0x4cd8 : mword 16)
    (mword_of_int (BO + 0x30) : mword 64) (LOAD (mword_of_int 28, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) bodc_4cd8 bocx_4cd8. Qed.

  (* 0x32  2705  addiw a4,a4,1 *)
  Lemma boi_32 : kernel_text -∗ instr (mword_of_int (BO + 0x32) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))).
  Proof. mk_rvc (BO + 0x32)%Z (mword_of_int 0x2705 : mword 16)
    (mword_of_int (BO + 0x32) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14))) bodc_2705 exec_execute_C_ADDIW. Qed.

  (* 0x34  0027179b  slliw a5,a4,0x2 *)
  Lemma boi_34 : kernel_text -∗ instr (mword_of_int (BO + 0x34) : mword 64) false (SHIFTIWOP (mword_of_int 2 : mword 5, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLIW)).
  Proof. mk_base (BO + 0x34)%Z (mword_of_int 0x0027179b : mword 32)
    (mword_of_int (BO + 0x34) : mword 64) (SHIFTIWOP (mword_of_int 2 : mword 5, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLIW)) bodb_0027179b. Qed.

  (* 0x38  9fb9  addw a5,a5,a4 *)
  Lemma boi_38 : kernel_text -∗ instr (mword_of_int (BO + 0x38) : mword 64) true (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ADDW)).
  Proof. mk_rvc (BO + 0x38)%Z (mword_of_int 0x9fb9 : mword 16)
    (mword_of_int (BO + 0x38) : mword 64) (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ADDW)) bodc_9fb9 exec_execute_C_ADDW. Qed.

  (* 0x3a  0017979b  slliw a5,a5,0x1 *)
  Lemma boi_3a : kernel_text -∗ instr (mword_of_int (BO + 0x3a) : mword 64) false (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLIW)).
  Proof. mk_base (BO + 0x3a)%Z (mword_of_int 0x0017979b : mword 32)
    (mword_of_int (BO + 0x3a) : mword 64) (SHIFTIWOP (mword_of_int 1 : mword 5, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLIW)) bodb_0017979b. Qed.

  (* 0x3e  54d4  lw a3,44(s1) *)
  Lemma boi_3e : kernel_text -∗ instr (mword_of_int (BO + 0x3e) : mword 64) true (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)).
  Proof. mk_rvc (BO + 0x3e)%Z (mword_of_int 0x54d4 : mword 16)
    (mword_of_int (BO + 0x3e) : mword 64) (LOAD (mword_of_int 44, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)) bodc_54d4 bocx_54d4. Qed.

  (* 0x40  9fb5  addw a5,a5,a3 *)
  Lemma boi_40 : kernel_text -∗ instr (mword_of_int (BO + 0x40) : mword 64) true (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ADDW)).
  Proof. mk_rvc (BO + 0x40)%Z (mword_of_int 0x9fb5 : mword 16)
    (mword_of_int (BO + 0x40) : mword 64) (RTYPEW (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ADDW)) bodc_9fb5 exec_execute_C_ADDW. Qed.

  (* 0x42  00f95763  bge s2,a5,80003c2a <begin_op+0x50> *)
  Lemma boi_42 : kernel_text -∗ instr (mword_of_int (BO + 0x42) : mword 64) false (BTYPE (mword_of_int 14 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE)).
  Proof. mk_base (BO + 0x42)%Z (mword_of_int 0x00f95763 : mword 32)
    (mword_of_int (BO + 0x42) : mword 64) (BTYPE (mword_of_int 14 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE)) bodb_00f95763. Qed.

  (* 0x46  85a6  mv a1,s1 *)
  Lemma boi_46 : kernel_text -∗ instr (mword_of_int (BO + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (BO + 0x46)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (BO + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* 0x48  8526  mv a0,s1 *)
  Lemma boi_48 : kernel_text -∗ instr (mword_of_int (BO + 0x48) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BO + 0x48)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (BO + 0x48) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x4a  ae2fe0ef  jal 80001f06 <sleep> *)
  Lemma boi_4a : kernel_text -∗ instr (mword_of_int (BO + 0x4a) : mword 64) false (JAL (mword_of_int 2089698 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BO + 0x4a)%Z (mword_of_int 0xae2fe0ef : mword 32)
    (mword_of_int (BO + 0x4a) : mword 64) (JAL (mword_of_int 2089698 : mword 21, Regidx (mword_of_int 1))) bodb_ae2fe0ef. Qed.

  (* 0x4e  bff9  j 80003c06 <begin_op+0x2c> *)
  Lemma boi_4e : kernel_text -∗ instr (mword_of_int (BO + 0x4e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BO + 0x4e)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (BO + 0x4e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

  (* 0x50  0001e797  auipc a5,0x1e *)
  Lemma boi_50 : kernel_text -∗ instr (mword_of_int (BO + 0x50) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (BO + 0x50)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (BO + 0x50) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x54  70e7a523  sw a4,1802(a5) # 80022334 <log+0x1c> *)
  Lemma boi_54 : kernel_text -∗ instr (mword_of_int (BO + 0x54) : mword 64) false (STORE (mword_of_int 1802 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_base (BO + 0x54)%Z (mword_of_int 0x70e7a523 : mword 32)
    (mword_of_int (BO + 0x54) : mword 64) (STORE (mword_of_int 1802 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) bodb_70e7a523. Qed.

  (* 0x58  0001e517  auipc a0,0x1e *)
  Lemma boi_58 : kernel_text -∗ instr (mword_of_int (BO + 0x58) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BO + 0x58)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (BO + 0x58) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x5c  6e650513  addi a0,a0,1766 # 80022318 <log> *)
  Lemma boi_5c : kernel_text -∗ instr (mword_of_int (BO + 0x5c) : mword 64) false (ITYPE (mword_of_int 1766 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BO + 0x5c)%Z (mword_of_int 0x6e650513 : mword 32)
    (mword_of_int (BO + 0x5c) : mword 64) (ITYPE (mword_of_int 1766 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bodb_6e650513. Qed.

  (* 0x60  856fd0ef  jal 80000c90 <release> *)
  Lemma boi_60 : kernel_text -∗ instr (mword_of_int (BO + 0x60) : mword 64) false (JAL (mword_of_int 2084950 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BO + 0x60)%Z (mword_of_int 0x856fd0ef : mword 32)
    (mword_of_int (BO + 0x60) : mword 64) (JAL (mword_of_int 2084950 : mword 21, Regidx (mword_of_int 1))) bodb_856fd0ef. Qed.

  (* 0x64  60e2  ld ra,24(sp) *)
  Lemma boi_64 : kernel_text -∗ instr (mword_of_int (BO + 0x64) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BO + 0x64)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (BO + 0x64) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  (* 0x66  6442  ld s0,16(sp) *)
  Lemma boi_66 : kernel_text -∗ instr (mword_of_int (BO + 0x66) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BO + 0x66)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (BO + 0x66) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  (* 0x68  64a2  ld s1,8(sp) *)
  Lemma boi_68 : kernel_text -∗ instr (mword_of_int (BO + 0x68) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BO + 0x68)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (BO + 0x68) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* 0x6a  6902  ld s2,0(sp) *)
  Lemma boi_6a : kernel_text -∗ instr (mword_of_int (BO + 0x6a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (BO + 0x6a)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (BO + 0x6a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  (* 0x6c  6105  addi sp,sp,32 *)
  Lemma boi_6c : kernel_text -∗ instr (mword_of_int (BO + 0x6c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BO + 0x6c)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (BO + 0x6c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* 0x6e  8082  ret *)
  Lemma boi_6e : kernel_text -∗ instr (mword_of_int (BO + 0x6e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BO + 0x6e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BO + 0x6e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End BeginOpInstrs.

(* CodeSysSync.v -- the instruction-DECODE layer for xv6's sys_sync().
   For EVERY instruction of

     sys_sync @ 0x80003e30 .. 0x80003e94   (offsets 0x00 .. 0x64, 102 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([ssi_<off>]) plus
   the per-instruction decode facts they consume ([ssdc_<word>] compressed /
   [ssdb_<word>] base / [sscx_<word>] the compressed leaf expansions).
   sys_sync is the syscall entry point of log.c; it is reached from syscall()'s
   dispatch table and calls only acquire / sleep / release.

   THE C SOURCE (xv6-riscv/kernel/log.c):

     uint64 sys_sync(void) {
       acquire(&log.lock);
       if (log.committing || log.outstanding > 0) {
         int n = log.ncommit + 1;
         while (log.ncommit < n) { sleep(&log, &log.lock); }
       }
       release(&log.lock);
       return 0;
     }

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

   Evidence in the image: the disassembler's own symbolisation of the six
   auipc/{addi,lw} pairs in THIS function -- [80022318 <log>] three times,
   [80022338 <log+0x20>] (committing), [80022334 <log+0x1c>] (outstanding),
   [80022340 <log+0x28>] (ncommit) -- plus the [lw a5,40(s1)] against s1 = &log
   that re-reads ncommit at the top of the sleep loop.  There is NO [size]
   field in this xv6's [struct log].  LOGBLOCKS = 30, so
   sizeof(logheader) = 4 + 4*30 = 124 and sizeof(log) = 48 + 124 = 172.

   Byte-exact disassembly (from the tracked kernel-rocq/KernelInstrs.v; it and
   xv6-riscv/kernel/kernel.asm agree byte for byte over this function):

     0x00 1101     addi sp,sp,-32
     0x02 ec06     sd ra,24(sp)
     0x04 e822     sd s0,16(sp)
     0x06 1000     addi s0,sp,32
     0x08 0001e517 auipc a0,0x1e
     0x0c 4e050513 addi a0,a0,1248 # 80022318 <log>
     0x10 dc9fc0ef jal 80000c08 <acquire>
     0x14 0001e797 auipc a5,0x1e
     0x18 4f47a783 lw a5,1268(a5) # 80022338 <log+0x20>   (log.committing)
     0x1c e799     bnez a5,80003e5a <sys_sync+0x2a>
     0x1e 0001e797 auipc a5,0x1e
     0x22 4e67a783 lw a5,1254(a5) # 80022334 <log+0x1c>   (log.outstanding)
     0x26 02f05563 blez a5,80003e80 <sys_sync+0x50>
     0x2a e426     sd s1,8(sp)
     0x2c e04a     sd s2,0(sp)
     0x2e 0001e917 auipc s2,0x1e
     0x32 4e292903 lw s2,1250(s2) # 80022340 <log+0x28>   (log.ncommit)
     0x36 0001e497 auipc s1,0x1e
     0x3a 4b248493 addi s1,s1,1202 # 80022318 <log>
     0x3e 85a6     mv a1,s1
     0x40 8526     mv a0,s1
     0x42 894fe0ef jal 80001f06 <sleep>
     0x46 549c     lw a5,40(s1)                           (log.ncommit)
     0x48 fef95be3 bge s2,a5,80003e6e <sys_sync+0x3e>
     0x4c 64a2     ld s1,8(sp)
     0x4e 6902     ld s2,0(sp)
     0x50 0001e517 auipc a0,0x1e
     0x54 49850513 addi a0,a0,1176 # 80022318 <log>
     0x58 e09fc0ef jal 80000c90 <release>
     0x5c 4501     li a0,0
     0x5e 60e2     ld ra,24(sp)
     0x60 6442     ld s0,16(sp)
     0x62 6105     addi sp,sp,32
     0x64 8082     ret

   STRUCTURE.
     Frame: 32 bytes ([c.addi sp,sp,-32] at +0x00, [c.addi16sp sp,32] at +0x62).
       Slots: ra@24(sp), s0@16(sp), s1@8(sp), s2@0(sp); s0 = sp+32 (frame ptr).
     THE s1/s2 SAVES ARE CONDITIONAL -- gcc SHRINK-WRAPPED them.  Only ra and
       s0 are saved in the prologue (+0x02/+0x04); [sd s1,8(sp)] and
       [sd s2,0(sp)] sit at +0x2a/+0x2c, i.e. INSIDE the taken-if arm, and the
       matching [ld s1,8(sp)] / [ld s2,0(sp)] at +0x4c/+0x4e are executed only
       on the way out of that arm.  The fall-through path (+0x26 blez taken ->
       +0x50) never touches those two stack slots and never clobbers s1/s2, so
       the callee-saved obligation is discharged differently on the two arms:
       by not-writing on the fast path, by save/restore on the sleeping path.
       The 32-byte frame is nevertheless allocated unconditionally.
     Register roles: a5 = the scratch that carries log.committing, then
       log.outstanding, then (in the loop) the re-read log.ncommit; s1 = &log
       (0x80022318), materialised at +0x36/+0x3a and reloaded on every
       iteration's sleep call; s2 = the ORIGINAL log.ncommit read once at
       +0x2e/+0x32 -- see the loop note below; a0/a1 = the call arguments.
     Log fields touched: READS log.committing(+32) @+0x18 (absolute, through
       the +0x14 auipc), log.outstanding(+28) @+0x22 (absolute, through the
       +0x1e auipc), log.ncommit(+40) @+0x32 (absolute, through the +0x2e
       auipc) and again @+0x46 (through s1).  WRITES none -- sys_sync only
       waits; it is the one log.c function that mutates no field of [log].
     Call sites (all four-byte [jal ra]):
       +0x10  jal acquire (0x80000c08)  a0 = &log.lock (= &log = 0x80022318)
       +0x42  jal sleep   (0x80001f06)  a0 = s1 (chan = &log), a1 = s1 (lk =
                                        &log.lock)
       +0x58  jal release (0x80000c90)  a0 = &log.lock (= &log)
     Loop (the C's [while (log.ncommit < n)] with [n = ncommit_0 + 1]):
       gcc did NOT materialise [n].  It kept s2 = the ORIGINAL log.ncommit
       (read once, before the loop) and compiled [ncommit < ncommit_0 + 1] as
       [ncommit <= ncommit_0], i.e. the SIGNED back edge [bge s2,a5] -- "loop
       again while old >= current".  So the exit condition is "the counter has
       strictly advanced past the value it had on entry", and the +1 exists
       nowhere in the code.  The loop is a do-while: it is ENTERED at its body
       (+0x3e), not at its test.
       entry   +0x36  (fall-through from the s2 read; s1 = &log is set up here)
       body    +0x3e..+0x44  (mv a1,s1 ; mv a0,s1 ; jal sleep)
       test    +0x46  lw a5,40(s1)   (re-read log.ncommit under the re-acquired
                                      lock that sleep returns holding)
       back    +0x48  bge s2,a5 -> +0x3e
       exit    +0x48  bge NOT taken -> fall into +0x4c (the s1/s2 restores)
       No induction variable: the loop terminates on another thread's write.
     Branch structure: exactly two conditional branches outside the loop --
       +0x1c  bnez a5 -> +0x2a   (log.committing != 0: take the sleeping arm)
       +0x26  blez a5 -> +0x50   (log.outstanding <= 0 AND not committing:
                                  skip straight to the release)
       plus the loop's +0x48 back edge.  There is no unconditional jump
       anywhere in the function.
     Return sites: one, the [c.ret] at +0x64; the return value is the [li a0,0]
       at +0x5c.
     NO PANIC SITE -- sys_sync contains no call to panic() and no unreachable
     tail; every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (15 words):
         0x1101, 0xec06, 0xe822, 0x1000, 0xe426, 0xe04a, 0x85a6, 0x8526,
         0x64a2, 0x6902, 0x4501, 0x60e2, 0x6442, 0x6105, 0x8082
     * KernelBaseDecode.v (3 words):
         0x0001e517, 0x0001e797, 0x0001e497

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     0x549c     -- also CodeEndOp.v:eodc_549c, CodeKilled.v:kldec_lw_killed
                   (and its leaf shape, CodeEndOp.v:eocx_549c)
     0x0001e917 -- also CodeInitlog.v:ildb_0001e917,
                   CodeVirtioDiskRw.v:rwb_0001e917
   Every other word below occurs in this function and nowhere else in the
   tree, so it stays local.
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
(* Compressed decode facts private to sys_sync.                          *)
(* ===================================================================== *)

(* 0xe799  bnez a5,80003e5a <sys_sync+0x2a>   (+14 bytes, so uimm = 7) *)
Lemma ssdc_e799 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe799 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 7, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x549c  lw a5,40(s1) *)
Lemma ssdc_549c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x549c : mword 16)) s
  = Some (C_LW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma sscx_549c s :
  exec (execute (C_LW (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to sys_sync.                       *)
(* ===================================================================== *)

(* 0x4e050513  addi a0,a0,1248 # 80022318 <log> *)
Lemma ssdb_4e050513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4e050513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1248 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xdc9fc0ef  jal 80000c08 <acquire>   (0x80003e40 - 12856) *)
Lemma ssdb_dc9fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdc9fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084296 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x4f47a783  lw a5,1268(a5) # 80022338 <log+0x20> *)
Lemma ssdb_4f47a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4f47a783 : mword 32)) s
  = Some (LOAD (mword_of_int 1268 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x4e67a783  lw a5,1254(a5) # 80022334 <log+0x1c> *)
Lemma ssdb_4e67a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4e67a783 : mword 32)) s
  = Some (LOAD (mword_of_int 1254 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x02f05563  blez a5,80003e80 <sys_sync+0x50>   (= bge x0,a5, +42) *)
Lemma ssdb_02f05563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f05563 : mword 32)) s
  = Some (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001e917  auipc s2,0x1e *)
Lemma ssdb_0001e917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e917 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x4e292903  lw s2,1250(s2) # 80022340 <log+0x28> *)
Lemma ssdb_4e292903 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4e292903 : mword 32)) s
  = Some (LOAD (mword_of_int 1250 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x4b248493  addi s1,s1,1202 # 80022318 <log> *)
Lemma ssdb_4b248493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4b248493 : mword 32)) s
  = Some (ITYPE (mword_of_int 1202 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x894fe0ef  jal 80001f06 <sleep>   (0x80003e72 - 8044) *)
Lemma ssdb_894fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x894fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089108 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfef95be3  bge s2,a5,80003e6e <sys_sync+0x3e>   (-10, i.e. 8192-10) *)
Lemma ssdb_fef95be3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfef95be3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x49850513  addi a0,a0,1176 # 80022318 <log> *)
Lemma ssdb_49850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x49850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1176 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xe09fc0ef  jal 80000c90 <release>   (0x80003e88 - 12792) *)
Lemma ssdb_e09fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe09fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084360 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysSyncInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* 0x00  1101  addi sp,sp,-32 *)
  Lemma ssi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  (* 0x02  ec06  sd ra,24(sp) *)
  Lemma ssi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  (* 0x04  e822  sd s0,16(sp) *)
  Lemma ssi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  (* 0x06  1000  addi s0,sp,32 *)
  Lemma ssi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x06)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* 0x08  0001e517  auipc a0,0x1e *)
  Lemma ssi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x08) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x08)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x08) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x0c  4e050513  addi a0,a0,1248 # 80022318 <log> *)
  Lemma ssi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x0c) : mword 64) false (ITYPE (mword_of_int 1248 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.sys_sync + 0x0c)%Z (mword_of_int 0x4e050513 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x0c) : mword 64) (ITYPE (mword_of_int 1248 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) ssdb_4e050513. Qed.

  (* 0x10  dc9fc0ef  jal 80000c08 <acquire> *)
  Lemma ssi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x10) : mword 64) false (JAL (mword_of_int 2084296 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.sys_sync + 0x10)%Z (mword_of_int 0xdc9fc0ef : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x10) : mword 64) (JAL (mword_of_int 2084296 : mword 21, Regidx (mword_of_int 1))) ssdb_dc9fc0ef. Qed.

  (* 0x14  0001e797  auipc a5,0x1e *)
  Lemma ssi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x14) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x14)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x14) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x18  4f47a783  lw a5,1268(a5) # 80022338 <log+0x20>  (log.committing) *)
  Lemma ssi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x18) : mword 64) false (LOAD (mword_of_int 1268 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (KernelSyms.sys_sync + 0x18)%Z (mword_of_int 0x4f47a783 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x18) : mword 64) (LOAD (mword_of_int 1268 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) ssdb_4f47a783. Qed.

  (* 0x1c  e799  bnez a5,80003e5a <sys_sync+0x2a> *)
  Lemma ssi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x1c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x1c)%Z (mword_of_int 0xe799 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x1c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 7 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) ssdc_e799 exec_execute_C_BNEZ. Qed.

  (* 0x1e  0001e797  auipc a5,0x1e *)
  Lemma ssi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x1e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x1e)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x1e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x22  4e67a783  lw a5,1254(a5) # 80022334 <log+0x1c>  (log.outstanding) *)
  Lemma ssi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x22) : mword 64) false (LOAD (mword_of_int 1254 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (KernelSyms.sys_sync + 0x22)%Z (mword_of_int 0x4e67a783 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x22) : mword 64) (LOAD (mword_of_int 1254 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) ssdb_4e67a783. Qed.

  (* 0x26  02f05563  blez a5,80003e80 <sys_sync+0x50> *)
  Lemma ssi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x26) : mword 64) false (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (KernelSyms.sys_sync + 0x26)%Z (mword_of_int 0x02f05563 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x26) : mword 64) (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) ssdb_02f05563. Qed.

  (* 0x2a  e426  sd s1,8(sp)   -- shrink-wrapped save *)
  Lemma ssi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x2a)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  (* 0x2c  e04a  sd s2,0(sp)   -- shrink-wrapped save *)
  Lemma ssi_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x2c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x2c)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x2c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  (* 0x2e  0001e917  auipc s2,0x1e *)
  Lemma ssi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x2e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x2e)%Z (mword_of_int 0x0001e917 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x2e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 18), AUIPC)) ssdb_0001e917. Qed.

  (* 0x32  4e292903  lw s2,1250(s2) # 80022340 <log+0x28>  (log.ncommit) *)
  Lemma ssi_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x32) : mword 64) false (LOAD (mword_of_int 1250 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), false, 4)).
  Proof. mk_base (KernelSyms.sys_sync + 0x32)%Z (mword_of_int 0x4e292903 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x32) : mword 64) (LOAD (mword_of_int 1250 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), false, 4)) ssdb_4e292903. Qed.

  (* 0x36  0001e497  auipc s1,0x1e *)
  Lemma ssi_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x36) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x36)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x36) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  (* 0x3a  4b248493  addi s1,s1,1202 # 80022318 <log> *)
  Lemma ssi_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x3a) : mword 64) false (ITYPE (mword_of_int 1202 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.sys_sync + 0x3a)%Z (mword_of_int 0x4b248493 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x3a) : mword 64) (ITYPE (mword_of_int 1202 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) ssdb_4b248493. Qed.

  (* 0x3e  85a6  mv a1,s1 *)
  Lemma ssi_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x3e)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* 0x40  8526  mv a0,s1 *)
  Lemma ssi_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x40) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x40)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x42  894fe0ef  jal 80001f06 <sleep> *)
  Lemma ssi_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x42) : mword 64) false (JAL (mword_of_int 2089108 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.sys_sync + 0x42)%Z (mword_of_int 0x894fe0ef : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x42) : mword 64) (JAL (mword_of_int 2089108 : mword 21, Regidx (mword_of_int 1))) ssdb_894fe0ef. Qed.

  (* 0x46  549c  lw a5,40(s1)  (log.ncommit, re-read) *)
  Lemma ssi_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x46) : mword 64) true (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x46)%Z (mword_of_int 0x549c : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x46) : mword 64) (LOAD (mword_of_int 40, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) ssdc_549c sscx_549c. Qed.

  (* 0x48  fef95be3  bge s2,a5,80003e6e <sys_sync+0x3e>  (the loop back edge) *)
  Lemma ssi_48 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x48) : mword 64) false (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE)).
  Proof. mk_base (KernelSyms.sys_sync + 0x48)%Z (mword_of_int 0xfef95be3 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x48) : mword 64) (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BGE)) ssdb_fef95be3. Qed.

  (* 0x4c  64a2  ld s1,8(sp)   -- shrink-wrapped restore *)
  Lemma ssi_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x4c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x4c)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x4c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* 0x4e  6902  ld s2,0(sp)   -- shrink-wrapped restore *)
  Lemma ssi_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x4e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x4e)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  (* 0x50  0001e517  auipc a0,0x1e *)
  Lemma ssi_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x50) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.sys_sync + 0x50)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x50) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x54  49850513  addi a0,a0,1176 # 80022318 <log> *)
  Lemma ssi_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x54) : mword 64) false (ITYPE (mword_of_int 1176 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.sys_sync + 0x54)%Z (mword_of_int 0x49850513 : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x54) : mword 64) (ITYPE (mword_of_int 1176 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) ssdb_49850513. Qed.

  (* 0x58  e09fc0ef  jal 80000c90 <release> *)
  Lemma ssi_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x58) : mword 64) false (JAL (mword_of_int 2084360 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.sys_sync + 0x58)%Z (mword_of_int 0xe09fc0ef : mword 32)
    (mword_of_int (KernelSyms.sys_sync + 0x58) : mword 64) (JAL (mword_of_int 2084360 : mword 21, Regidx (mword_of_int 1))) ssdb_e09fc0ef. Qed.

  (* 0x5c  4501  li a0,0   (the return value) *)
  Lemma ssi_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x5c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x5c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x5c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* 0x5e  60e2  ld ra,24(sp) *)
  Lemma ssi_5e : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x5e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x5e)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x5e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  (* 0x60  6442  ld s0,16(sp) *)
  Lemma ssi_60 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x60) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x60)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x60) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  (* 0x62  6105  addi sp,sp,32 *)
  Lemma ssi_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x62) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x62)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x62) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* 0x64  8082  ret *)
  Lemma ssi_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.sys_sync + 0x64) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.sys_sync + 0x64)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.sys_sync + 0x64) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End SysSyncInstrs.

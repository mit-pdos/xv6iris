(* CodeLogWrite.v -- the instruction-DECODE layer for xv6's log_write().
   For EVERY instruction of

     log_write @ 0x80003d6c .. 0x80003e2e  (offsets 0x00 .. 0xc2, 196 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([lwi_<off>]) plus
   the per-instruction decode facts they consume ([lwdc_<word>] compressed /
   [lwdb_<word>] base / [lwcx_<word>] the compressed leaf expansions).
   log_write ends at sys_sync (0x80003e30), which is deferred.

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
     0x08 1000     addi s0,sp,32
     0x0a 84aa     mv s1,a0
     0x0c 0001e517 auipc a0,0x1e
     0x10 5a050513 addi a0,a0,1440 # 80022318 <log>
     0x14 e89fc0ef jal 80000c08 <acquire>
     0x18 0001e617 auipc a2,0x1e
     0x1c 5c062603 lw a2,1472(a2) # 80022344 <log+0x2c>
     0x20 47f5     li a5,29
     0x22 04c7cd63 blt a5,a2,80003de8 <log_write+0x7c>
     0x26 0001e797 auipc a5,0x1e
     0x2a 5a27a783 lw a5,1442(a5) # 80022334 <log+0x1c>
     0x2e 04f05d63 blez a5,80003df4 <log_write+0x88>
     0x32 4781     li a5,0
     0x34 06c05063 blez a2,80003e00 <log_write+0x94>
     0x38 44cc     lw a1,12(s1)
     0x3a 0001e717 auipc a4,0x1e
     0x3e 5a270713 addi a4,a4,1442 # 80022348 <log+0x30>
     0x42 4781     li a5,0
     0x44 4314     lw a3,0(a4)
     0x46 04b68763 beq a3,a1,80003e00 <log_write+0x94>
     0x4a 2785     addiw a5,a5,1
     0x4c 0711     addi a4,a4,4
     0x4e fef61be3 bne a2,a5,80003db0 <log_write+0x44>
     0x52 060a     slli a2,a2,0x2
     0x54 02060613 addi a2,a2,32
     0x58 0001e797 auipc a5,0x1e
     0x5c 55478793 addi a5,a5,1364 # 80022318 <log>
     0x60 97b2     add a5,a5,a2
     0x62 44d8     lw a4,12(s1)
     0x64 cb98     sw a4,16(a5)
     0x66 8526     mv a0,s1
     0x68 eeffe0ef jal 80002cc2 <bpin>
     0x6c 0001e717 auipc a4,0x1e
     0x70 54070713 addi a4,a4,1344 # 80022318 <log>
     0x74 575c     lw a5,44(a4)
     0x76 2785     addiw a5,a5,1
     0x78 d75c     sw a5,44(a4)
     0x7a a815     j 80003e1a <log_write+0xae>
     0x7c 00003517 auipc a0,0x3
     0x80 72850513 addi a0,a0,1832 # 80007510 <etext+0x510>
     0x84 a37fc0ef jal 80000826 <panic>
     0x88 00003517 auipc a0,0x3
     0x8c 73450513 addi a0,a0,1844 # 80007528 <etext+0x528>
     0x90 a2bfc0ef jal 80000826 <panic>
     0x94 00279693 slli a3,a5,0x2
     0x98 02068693 addi a3,a3,32
     0x9c 0001e717 auipc a4,0x1e
     0xa0 51070713 addi a4,a4,1296 # 80022318 <log>
     0xa4 9736     add a4,a4,a3
     0xa6 44d4     lw a3,12(s1)
     0xa8 cb14     sw a3,16(a4)
     0xaa faf60ee3 beq a2,a5,80003dd2 <log_write+0x66>
     0xae 0001e517 auipc a0,0x1e
     0xb2 4fe50513 addi a0,a0,1278 # 80022318 <log>
     0xb6 e6ffc0ef jal 80000c90 <release>
     0xba 60e2     ld ra,24(sp)
     0xbc 6442     ld s0,16(sp)
     0xbe 64a2     ld s1,8(sp)
     0xc0 6105     addi sp,sp,32
     0xc2 8082     ret

   STRUCTURE.
     Frame: 32 bytes ([c.addi sp,sp,-32] at +0x00, [c.addi16sp sp,32] at +0xc0).
       Saved: ra@24, s0@16, s1@8; s0 = sp+32.  NOTE only ONE callee-saved
       register besides s0 -- there is no s2 in this function.
     Register roles: s1 = the [b] argument (from a0 at +0x0a); a2 = log.lh.n,
       and later 4*n+32 (the byte displacement of &log.lh.block[n] from &log
       minus 16); a5 = the loop index i, and later the address &log + 4*n + 32;
       a4 = the walking cursor &log.lh.block[i], and later &log + 4*i + 32;
       a1 = b->blockno; a3 = log.lh.block[i] / b->blockno.
     Log fields touched: READS log.lh.n(+44) @+0x1c (through its own auipc, at
       0x80022344) and @+0x74 (as 44(a4)), log.outstanding(+28) @+0x2a (through
       its own auipc, at 0x80022334), log.lh.block[i](+48+4i) @+0x44.
       WRITES log.lh.block[i] @+0x64 and @+0xa8 -- both spelled [sw *,16(reg)]
       where reg = &log + 4*index + 32, i.e. 32+16 = 48 = the lh.block offset --
       and log.lh.n(+44) @+0x78 (n += 1).
     Buffer field: b->blockno at 12(s1), read at +0x38, +0x62 and +0xa6.
     Constants: [li a5,29] at +0x20 is LOGBLOCKS-1 (LOGBLOCKS = 30).
     Call sites (all four-byte [jal ra]):
       +0x14  jal acquire (0x80000c08)  a0 = &log.lock (= &log = 0x80022318)
       +0x68  jal bpin    (0x80002cc2)  a0 = s1 (b)
       +0x84  jal panic   (0x80000826)  a0 = 0x80007510 "too big a transaction"
       +0x90  jal panic   (0x80000826)  a0 = 0x80007528 "log_write outside of
                                             trans"
       +0xb6  jal release (0x80000c90)  a0 = &log.lock (= &log)
     PANIC SITES: two, both after their own auipc/addi pair --
       +0x7c..+0x84  0x80007510 "too big a transaction"     (log.lh.n >= 30)
       +0x88..+0x90  0x80007528 "log_write outside of trans" (outstanding < 1)
     Loop (the absorption scan [for (i = 0; i < log.lh.n; i++)]):
       guard   +0x34  blez a2 -> +0x94   (n <= 0: i stays 0, go straight to the
                                          [log.lh.block[i] = b->blockno] store)
       setup   +0x38..+0x42 (a1 = b->blockno, a4 = &log.lh.block[0], a5 = 0)
       top     +0x44  lw a3,0(a4)
       break   +0x46  beq a3,a1 -> +0x94  (absorption hit: keep this i)
       bump    +0x4a  addiw a5,a5,1 ; +0x4c  addi a4,a4,4
       back    +0x4e  bne a2,a5 -> +0x44
       exit    +0x52  (fall-through: i == n, the "append" path)
       induction variable: a5 (i), with a4 = &log.lh.block[i] in lock step;
       the bound is a2 = log.lh.n, loaded once at +0x1c.
     THE TWO STORE PATHS.  gcc duplicated [log.lh.block[i] = b->blockno]:
       APPEND (+0x52..+0x64), reached by falling out of the loop with i == n,
         addresses the slot from a2 = 4*n (a2 = log.lh.n <<2, +32, + &log), and
         falls straight into the bpin / [log.lh.n++] block at +0x66..+0x78,
         then [j +0xae];
       ABSORB (+0x94..+0xaa), reached from the +0x34 guard or the +0x46 break,
         addresses the slot from a5 = i the same way, then
         +0xaa  beq a2,a5 -> +0x66 -- if i turned out to equal n after all
         (the n == 0 entry from +0x34), it JOINS the append path's bpin block;
         otherwise it falls through to the release at +0xae.
     Branch structure: +0x22 (blt a5,a2 -> panic), +0x2e (blez a5 -> panic),
       +0x34 (blez a2 -> absorb path), +0x46 (beq -> absorb path),
       +0x4e (bne -> loop back edge), +0x7a (j -> release),
       +0xaa (beq -> the bpin block).
     Return sites: one, the [c.ret] at +0xc2 (plus the two non-returning panics).
     Every instruction is reachable.

   SHARED WORDS.  These are already proved at the shared altitude and are
   NOT re-proved here (the DECODE-WORD DEDUP SWEEP rule in
   claude-notes/durable-notes.md; the search was by STATEMENT over every
   iris/*.v, not by word, so offset-named homes were seen too):
     * KernelRvcDecode.v (15 words):
         0x1101, 0xec06, 0xe822, 0xe426, 0x1000, 0x84aa, 0x4781, 0x2785,
         0x8526, 0x9736, 0x60e2, 0x6442, 0x64a2, 0x6105, 0x8082
     * KernelBaseDecode.v (3 words):
         0x0001e517, 0x0001e797, 0x0001e717

   DUPLICATION NOTED, DELIBERATELY NOT PROMOTED.  Each word below is proved
   privately here AND has at least one other private home in the tree; the
   rule says such a word belongs in KernelRvcDecode.v / KernelBaseDecode.v,
   but promoting it would edit files outside this task, so it is only
   recorded:
     (none)
   PROMOTED by the log.c decode-word dedup sweep.  Each word below was
   duplicated WITHIN the six log.c decode files and now lives once in
   KernelRvcDecode.v (compressed) / KernelBaseDecode.v (base), together with
   its leaf-shape expansion where that was duplicated too.  The local name is
   kept here as a RESTATEMENT with its original statement, closed by [exact]
   over the promoted lemma, so every consumer compiles untouched:
     0x4314 (+ write_head), 0x0711 (+ write_head, initlog),
     0x060a (+ write_head, initlog)
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
(* Compressed decode facts private to log_write.                    *)
(* ===================================================================== *)

(* 0x47f5  li a5,29 *)
Lemma lwdc_47f5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x47f5 : mword 16)) s
  = Some (C_LI (mword_of_int 29, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44cc  lw a1,12(s1) *)
Lemma lwdc_44cc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44cc : mword 16)) s
  = Some (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4314  lw a3,0(a4) *)
Lemma lwdc_4314 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4314 : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)), s).
Proof. exact (KernelRvcDecode.cdec_4314 s). Qed.

(* 0x0711  addi a4,a4,4 *)
Lemma lwdc_0711 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0711 : mword 16)) s
  = Some (C_ADDI (mword_of_int 4, Regidx (mword_of_int 14)), s).
Proof. exact (KernelRvcDecode.cdec_0711 s). Qed.

(* 0x060a  slli a2,a2,0x2 *)
Lemma lwdc_060a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x060a : mword 16)) s
  = Some (C_SLLI (mword_of_int 2, Regidx (mword_of_int 12)), s).
Proof. exact (KernelRvcDecode.cdec_060a s). Qed.

(* 0x97b2  add a5,a5,a2 *)
Lemma lwdc_97b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97b2 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44d8  lw a4,12(s1) *)
Lemma lwdc_44d8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44d8 : mword 16)) s
  = Some (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcb98  sw a4,16(a5) *)
Lemma lwdc_cb98 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb98 : mword 16)) s
  = Some (C_SW (mword_of_int 4, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x575c  lw a5,44(a4) *)
Lemma lwdc_575c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x575c : mword 16)) s
  = Some (C_LW (mword_of_int 11, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xd75c  sw a5,44(a4) *)
Lemma lwdc_d75c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd75c : mword 16)) s
  = Some (C_SW (mword_of_int 11, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa815  j 80003e1a <log_write+0xae> *)
Lemma lwdc_a815 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa815 : mword 16)) s
  = Some (C_J (mword_of_int 26), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44d4  lw a3,12(s1) *)
Lemma lwdc_44d4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44d4 : mword 16)) s
  = Some (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcb14  sw a3,16(a4) *)
Lemma lwdc_cb14 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb14 : mword 16)) s
  = Some (C_SW (mword_of_int 4, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- the leaf-form expansions of the compressed loads/stores: a literal
   [mword 12] displacement and plain [Regidx]es, the shape the WP
   load/store leaves take. ---- *)

Lemma lwcx_44cc s :
  exec (execute (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 3)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_4314 s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)), s).
Proof. exact (KernelRvcDecode.cexec_4314 s). Qed.

Lemma lwcx_44d8 s :
  exec (execute (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_cb98 s :
  exec (execute (C_SW (mword_of_int 4, Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)))) s
  = Some (ExecuteAs (STORE (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_575c s :
  exec (execute (C_LW (mword_of_int 11, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 44, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_d75c s :
  exec (execute (C_SW (mword_of_int 11, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 44, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_44d4 s :
  exec (execute (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma lwcx_cb14 s :
  exec (execute (C_SW (mword_of_int 4, Cregidx (mword_of_int 6), Cregidx (mword_of_int 5)))) s
  = Some (ExecuteAs (STORE (mword_of_int 16, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts private to log_write.                  *)
(* ===================================================================== *)

(* 0x5a050513  addi a0,a0,1440 # 80022318 <log> *)
Lemma lwdb_5a050513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5a050513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1440 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xe89fc0ef  jal 80000c08 <acquire> *)
Lemma lwdb_e89fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe89fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084488 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x0001e617  auipc a2,0x1e *)
Lemma lwdb_0001e617 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001e617 : mword 32)) s
  = Some (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 12), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x5c062603  lw a2,1472(a2) # 80022344 <log+0x2c> *)
Lemma lwdb_5c062603 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5c062603 : mword 32)) s
  = Some (LOAD (mword_of_int 1472 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x04c7cd63  blt a5,a2,80003de8 <log_write+0x7c> *)
Lemma lwdb_04c7cd63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04c7cd63 : mword 32)) s
  = Some (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

(* 0x5a27a783  lw a5,1442(a5) # 80022334 <log+0x1c> *)
Lemma lwdb_5a27a783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5a27a783 : mword 32)) s
  = Some (LOAD (mword_of_int 1442 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* 0x04f05d63  blez a5,80003df4 <log_write+0x88> *)
Lemma lwdb_04f05d63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04f05d63 : mword 32)) s
  = Some (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x06c05063  blez a2,80003e00 <log_write+0x94> *)
Lemma lwdb_06c05063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06c05063 : mword 32)) s
  = Some (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.

(* 0x5a270713  addi a4,a4,1442 # 80022348 <log+0x30> *)
Lemma lwdb_5a270713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5a270713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x04b68763  beq a3,a1,80003e00 <log_write+0x94> *)
Lemma lwdb_04b68763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04b68763 : mword 32)) s
  = Some (BTYPE (mword_of_int 78 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 13), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xfef61be3  bne a2,a5,80003db0 <log_write+0x44> *)
Lemma lwdb_fef61be3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfef61be3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BNE), s).
Proof. decode_bridge_ms. Qed.

(* 0x02060613  addi a2,a2,32 *)
Lemma lwdb_02060613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02060613 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x55478793  addi a5,a5,1364 # 80022318 <log> *)
Lemma lwdb_55478793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x55478793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1364 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xeeffe0ef  jal 80002cc2 <bpin> *)
Lemma lwdb_eeffe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeeffe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092782 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x54070713  addi a4,a4,1344 # 80022318 <log> *)
Lemma lwdb_54070713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x54070713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1344 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x00003517  auipc a0,0x3 *)
Lemma lwdb_00003517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00003517 : mword 32)) s
  = Some (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* 0x72850513  addi a0,a0,1832 # 80007510 <etext+0x510> *)
Lemma lwdb_72850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x72850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1832 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xa37fc0ef  jal 80000826 <panic> *)
Lemma lwdb_a37fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa37fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083382 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x73450513  addi a0,a0,1844 # 80007528 <etext+0x528> *)
Lemma lwdb_73450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x73450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1844 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xa2bfc0ef  jal 80000826 <panic> *)
Lemma lwdb_a2bfc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa2bfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083370 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x00279693  slli a3,a5,0x2 *)
Lemma lwdb_00279693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00279693 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 13), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x02068693  addi a3,a3,32 *)
Lemma lwdb_02068693 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02068693 : mword 32)) s
  = Some (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x51070713  addi a4,a4,1296 # 80022318 <log> *)
Lemma lwdb_51070713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x51070713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1296 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xfaf60ee3  beq a2,a5,80003dd2 <log_write+0x66> *)
Lemma lwdb_faf60ee3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaf60ee3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8124 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x4fe50513  addi a0,a0,1278 # 80022318 <log> *)
Lemma lwdb_4fe50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4fe50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1278 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0xe6ffc0ef  jal 80000c90 <release> *)
Lemma lwdb_e6ffc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe6ffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084462 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section LogWriteInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* 0x00  1101  addi sp,sp,-32 *)
  Lemma lwi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  (* 0x02  ec06  sd ra,24(sp) *)
  Lemma lwi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  (* 0x04  e822  sd s0,16(sp) *)
  Lemma lwi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  (* 0x06  e426  sd s1,8(sp) *)
  Lemma lwi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  (* 0x08  1000  addi s0,sp,32 *)
  Lemma lwi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* 0x0a  84aa  mv s1,a0 *)
  Lemma lwi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.log_write + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* 0x0c  0001e517  auipc a0,0x1e *)
  Lemma lwi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x0c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x0c)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x0c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0x10  5a050513  addi a0,a0,1440 # 80022318 <log> *)
  Lemma lwi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x10) : mword 64) false (ITYPE (mword_of_int 1440 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x10)%Z (mword_of_int 0x5a050513 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x10) : mword 64) (ITYPE (mword_of_int 1440 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) lwdb_5a050513. Qed.

  (* 0x14  e89fc0ef  jal 80000c08 <acquire> *)
  Lemma lwi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x14) : mword 64) false (JAL (mword_of_int 2084488 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.log_write + 0x14)%Z (mword_of_int 0xe89fc0ef : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x14) : mword 64) (JAL (mword_of_int 2084488 : mword 21, Regidx (mword_of_int 1))) lwdb_e89fc0ef. Qed.

  (* 0x18  0001e617  auipc a2,0x1e *)
  Lemma lwi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x18) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 12), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x18)%Z (mword_of_int 0x0001e617 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x18) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 12), AUIPC)) lwdb_0001e617. Qed.

  (* 0x1c  5c062603  lw a2,1472(a2) # 80022344 <log+0x2c> *)
  Lemma lwi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x1c) : mword 64) false (LOAD (mword_of_int 1472 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), false, 4)).
  Proof. mk_base (KernelSyms.log_write + 0x1c)%Z (mword_of_int 0x5c062603 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x1c) : mword 64) (LOAD (mword_of_int 1472 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), false, 4)) lwdb_5c062603. Qed.

  (* 0x20  47f5  li a5,29 *)
  Lemma lwi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 29 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x20)%Z (mword_of_int 0x47f5 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 29 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) lwdc_47f5 exec_execute_C_LI. Qed.

  (* 0x22  04c7cd63  blt a5,a2,80003de8 <log_write+0x7c> *)
  Lemma lwi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x22) : mword 64) false (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (KernelSyms.log_write + 0x22)%Z (mword_of_int 0x04c7cd63 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x22) : mword 64) (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 15), BLT)) lwdb_04c7cd63. Qed.

  (* 0x26  0001e797  auipc a5,0x1e *)
  Lemma lwi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x26) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x26)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x26) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x2a  5a27a783  lw a5,1442(a5) # 80022334 <log+0x1c> *)
  Lemma lwi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x2a) : mword 64) false (LOAD (mword_of_int 1442 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (KernelSyms.log_write + 0x2a)%Z (mword_of_int 0x5a27a783 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x2a) : mword 64) (LOAD (mword_of_int 1442 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), false, 4)) lwdb_5a27a783. Qed.

  (* 0x2e  04f05d63  blez a5,80003df4 <log_write+0x88> *)
  Lemma lwi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x2e) : mword 64) false (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (KernelSyms.log_write + 0x2e)%Z (mword_of_int 0x04f05d63 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x2e) : mword 64) (BTYPE (mword_of_int 90 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 0), BGE)) lwdb_04f05d63. Qed.

  (* 0x32  4781  li a5,0 *)
  Lemma lwi_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x32) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x32)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x32) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  (* 0x34  06c05063  blez a2,80003e00 <log_write+0x94> *)
  Lemma lwi_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x34) : mword 64) false (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (KernelSyms.log_write + 0x34)%Z (mword_of_int 0x06c05063 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x34) : mword 64) (BTYPE (mword_of_int 96 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 0), BGE)) lwdb_06c05063. Qed.

  (* 0x38  44cc  lw a1,12(s1) *)
  Lemma lwi_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x38) : mword 64) true (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), false, 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x38)%Z (mword_of_int 0x44cc : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x38) : mword 64) (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), false, 4)) lwdc_44cc lwcx_44cc. Qed.

  (* 0x3a  0001e717  auipc a4,0x1e *)
  Lemma lwi_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x3a) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x3a)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x3a) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  (* 0x3e  5a270713  addi a4,a4,1442 # 80022348 <log+0x30> *)
  Lemma lwi_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x3e) : mword 64) false (ITYPE (mword_of_int 1442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x3e)%Z (mword_of_int 0x5a270713 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x3e) : mword 64) (ITYPE (mword_of_int 1442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) lwdb_5a270713. Qed.

  (* 0x42  4781  li a5,0 *)
  Lemma lwi_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x42) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x42)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x42) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  (* 0x44  4314  lw a3,0(a4) *)
  Lemma lwi_44 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x44) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x44)%Z (mword_of_int 0x4314 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x44) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 14), Regidx (mword_of_int 13), false, 4)) lwdc_4314 lwcx_4314. Qed.

  (* 0x46  04b68763  beq a3,a1,80003e00 <log_write+0x94> *)
  Lemma lwi_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x46) : mword 64) false (BTYPE (mword_of_int 78 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 13), BEQ)).
  Proof. mk_base (KernelSyms.log_write + 0x46)%Z (mword_of_int 0x04b68763 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x46) : mword 64) (BTYPE (mword_of_int 78 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 13), BEQ)) lwdb_04b68763. Qed.

  (* 0x4a  2785  addiw a5,a5,1 *)
  Lemma lwi_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x4a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (KernelSyms.log_write + 0x4a)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x4a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  (* 0x4c  0711  addi a4,a4,4 *)
  Lemma lwi_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x4c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x4c)%Z (mword_of_int 0x0711 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x4c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) lwdc_0711 exec_execute_C_ADDI. Qed.

  (* 0x4e  fef61be3  bne a2,a5,80003db0 <log_write+0x44> *)
  Lemma lwi_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x4e) : mword 64) false (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BNE)).
  Proof. mk_base (KernelSyms.log_write + 0x4e)%Z (mword_of_int 0xfef61be3 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x4e) : mword 64) (BTYPE (mword_of_int 8182 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BNE)) lwdb_fef61be3. Qed.

  (* 0x52  060a  slli a2,a2,0x2 *)
  Lemma lwi_52 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x52) : mword 64) true (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (KernelSyms.log_write + 0x52)%Z (mword_of_int 0x060a : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x52) : mword 64) (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) lwdc_060a exec_execute_C_SLLI. Qed.

  (* 0x54  02060613  addi a2,a2,32 *)
  Lemma lwi_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x54) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x54)%Z (mword_of_int 0x02060613 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x54) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 12), Regidx (mword_of_int 12), ADDI)) lwdb_02060613. Qed.

  (* 0x58  0001e797  auipc a5,0x1e *)
  Lemma lwi_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x58) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x58)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x58) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  (* 0x5c  55478793  addi a5,a5,1364 # 80022318 <log> *)
  Lemma lwi_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x5c) : mword 64) false (ITYPE (mword_of_int 1364 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x5c)%Z (mword_of_int 0x55478793 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x5c) : mword 64) (ITYPE (mword_of_int 1364 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) lwdb_55478793. Qed.

  (* 0x60  97b2  add a5,a5,a2 *)
  Lemma lwi_60 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x60) : mword 64) true (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.log_write + 0x60)%Z (mword_of_int 0x97b2 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x60) : mword 64) (RTYPE (Regidx (mword_of_int 12), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) lwdc_97b2 exec_execute_C_ADD. Qed.

  (* 0x62  44d8  lw a4,12(s1) *)
  Lemma lwi_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x62) : mword 64) true (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x62)%Z (mword_of_int 0x44d8 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x62) : mword 64) (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) lwdc_44d8 lwcx_44d8. Qed.

  (* 0x64  cb98  sw a4,16(a5) *)
  Lemma lwi_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x64) : mword 64) true (STORE (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x64)%Z (mword_of_int 0xcb98 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x64) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 4)) lwdc_cb98 lwcx_cb98. Qed.

  (* 0x66  8526  mv a0,s1 *)
  Lemma lwi_66 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.log_write + 0x66)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* 0x68  eeffe0ef  jal 80002cc2 <bpin> *)
  Lemma lwi_68 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x68) : mword 64) false (JAL (mword_of_int 2092782 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.log_write + 0x68)%Z (mword_of_int 0xeeffe0ef : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x68) : mword 64) (JAL (mword_of_int 2092782 : mword 21, Regidx (mword_of_int 1))) lwdb_eeffe0ef. Qed.

  (* 0x6c  0001e717  auipc a4,0x1e *)
  Lemma lwi_6c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x6c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x6c)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x6c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  (* 0x70  54070713  addi a4,a4,1344 # 80022318 <log> *)
  Lemma lwi_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x70) : mword 64) false (ITYPE (mword_of_int 1344 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x70)%Z (mword_of_int 0x54070713 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x70) : mword 64) (ITYPE (mword_of_int 1344 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) lwdb_54070713. Qed.

  (* 0x74  575c  lw a5,44(a4) *)
  Lemma lwi_74 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x74) : mword 64) true (LOAD (mword_of_int 44, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x74)%Z (mword_of_int 0x575c : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x74) : mword 64) (LOAD (mword_of_int 44, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)) lwdc_575c lwcx_575c. Qed.

  (* 0x76  2785  addiw a5,a5,1 *)
  Lemma lwi_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x76) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (KernelSyms.log_write + 0x76)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x76) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  (* 0x78  d75c  sw a5,44(a4) *)
  Lemma lwi_78 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x78) : mword 64) true (STORE (mword_of_int 44, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0x78)%Z (mword_of_int 0xd75c : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x78) : mword 64) (STORE (mword_of_int 44, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) lwdc_d75c lwcx_d75c. Qed.

  (* 0x7a  a815  j 80003e1a <log_write+0xae> *)
  Lemma lwi_7a : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x7a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 26 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.log_write + 0x7a)%Z (mword_of_int 0xa815 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0x7a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 26 : mword 11) ('b"0")), zreg)) lwdc_a815 exec_execute_C_J. Qed.

  (* 0x7c  00003517  auipc a0,0x3 *)
  Lemma lwi_7c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x7c) : mword 64) false (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x7c)%Z (mword_of_int 0x00003517 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x7c) : mword 64) (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 10), AUIPC)) lwdb_00003517. Qed.

  (* 0x80  72850513  addi a0,a0,1832 # 80007510 <etext+0x510> *)
  Lemma lwi_80 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x80) : mword 64) false (ITYPE (mword_of_int 1832 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x80)%Z (mword_of_int 0x72850513 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x80) : mword 64) (ITYPE (mword_of_int 1832 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) lwdb_72850513. Qed.

  (* 0x84  a37fc0ef  jal 80000826 <panic> *)
  Lemma lwi_84 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x84) : mword 64) false (JAL (mword_of_int 2083382 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.log_write + 0x84)%Z (mword_of_int 0xa37fc0ef : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x84) : mword 64) (JAL (mword_of_int 2083382 : mword 21, Regidx (mword_of_int 1))) lwdb_a37fc0ef. Qed.

  (* 0x88  00003517  auipc a0,0x3 *)
  Lemma lwi_88 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x88) : mword 64) false (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x88)%Z (mword_of_int 0x00003517 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x88) : mword 64) (UTYPE (mword_of_int 3 : mword 20, Regidx (mword_of_int 10), AUIPC)) lwdb_00003517. Qed.

  (* 0x8c  73450513  addi a0,a0,1844 # 80007528 <etext+0x528> *)
  Lemma lwi_8c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x8c) : mword 64) false (ITYPE (mword_of_int 1844 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x8c)%Z (mword_of_int 0x73450513 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x8c) : mword 64) (ITYPE (mword_of_int 1844 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) lwdb_73450513. Qed.

  (* 0x90  a2bfc0ef  jal 80000826 <panic> *)
  Lemma lwi_90 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x90) : mword 64) false (JAL (mword_of_int 2083370 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.log_write + 0x90)%Z (mword_of_int 0xa2bfc0ef : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x90) : mword 64) (JAL (mword_of_int 2083370 : mword 21, Regidx (mword_of_int 1))) lwdb_a2bfc0ef. Qed.

  (* 0x94  00279693  slli a3,a5,0x2 *)
  Lemma lwi_94 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x94) : mword 64) false (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 13), SLLI)).
  Proof. mk_base (KernelSyms.log_write + 0x94)%Z (mword_of_int 0x00279693 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x94) : mword 64) (SHIFTIOP (mword_of_int 2 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 13), SLLI)) lwdb_00279693. Qed.

  (* 0x98  02068693  addi a3,a3,32 *)
  Lemma lwi_98 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x98) : mword 64) false (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0x98)%Z (mword_of_int 0x02068693 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x98) : mword 64) (ITYPE (mword_of_int 32 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADDI)) lwdb_02068693. Qed.

  (* 0x9c  0001e717  auipc a4,0x1e *)
  Lemma lwi_9c : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0x9c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0x9c)%Z (mword_of_int 0x0001e717 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0x9c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_0001e717. Qed.

  (* 0xa0  51070713  addi a4,a4,1296 # 80022318 <log> *)
  Lemma lwi_a0 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xa0) : mword 64) false (ITYPE (mword_of_int 1296 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0xa0)%Z (mword_of_int 0x51070713 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0xa0) : mword 64) (ITYPE (mword_of_int 1296 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) lwdb_51070713. Qed.

  (* 0xa4  9736  add a4,a4,a3 *)
  Lemma lwi_a4 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xa4) : mword 64) true (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (KernelSyms.log_write + 0xa4)%Z (mword_of_int 0x9736 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xa4) : mword 64) (RTYPE (Regidx (mword_of_int 13), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) cdec_9736 exec_execute_C_ADD. Qed.

  (* 0xa6  44d4  lw a3,12(s1) *)
  Lemma lwi_a6 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xa6) : mword 64) true (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0xa6)%Z (mword_of_int 0x44d4 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xa6) : mword 64) (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 13), false, 4)) lwdc_44d4 lwcx_44d4. Qed.

  (* 0xa8  cb14  sw a3,16(a4) *)
  Lemma lwi_a8 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xa8) : mword 64) true (STORE (mword_of_int 16, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)).
  Proof. mk_rvc (KernelSyms.log_write + 0xa8)%Z (mword_of_int 0xcb14 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xa8) : mword 64) (STORE (mword_of_int 16, Regidx (mword_of_int 13), Regidx (mword_of_int 14), 4)) lwdc_cb14 lwcx_cb14. Qed.

  (* 0xaa  faf60ee3  beq a2,a5,80003dd2 <log_write+0x66> *)
  Lemma lwi_aa : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xaa) : mword 64) false (BTYPE (mword_of_int 8124 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BEQ)).
  Proof. mk_base (KernelSyms.log_write + 0xaa)%Z (mword_of_int 0xfaf60ee3 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0xaa) : mword 64) (BTYPE (mword_of_int 8124 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 12), BEQ)) lwdb_faf60ee3. Qed.

  (* 0xae  0001e517  auipc a0,0x1e *)
  Lemma lwi_ae : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xae) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (KernelSyms.log_write + 0xae)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0xae) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  (* 0xb2  4fe50513  addi a0,a0,1278 # 80022318 <log> *)
  Lemma lwi_b2 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xb2) : mword 64) false (ITYPE (mword_of_int 1278 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.log_write + 0xb2)%Z (mword_of_int 0x4fe50513 : mword 32)
    (mword_of_int (KernelSyms.log_write + 0xb2) : mword 64) (ITYPE (mword_of_int 1278 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) lwdb_4fe50513. Qed.

  (* 0xb6  e6ffc0ef  jal 80000c90 <release> *)
  Lemma lwi_b6 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xb6) : mword 64) false (JAL (mword_of_int 2084462 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.log_write + 0xb6)%Z (mword_of_int 0xe6ffc0ef : mword 32)
    (mword_of_int (KernelSyms.log_write + 0xb6) : mword 64) (JAL (mword_of_int 2084462 : mword 21, Regidx (mword_of_int 1))) lwdb_e6ffc0ef. Qed.

  (* 0xba  60e2  ld ra,24(sp) *)
  Lemma lwi_ba : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xba) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0xba)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xba) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  (* 0xbc  6442  ld s0,16(sp) *)
  Lemma lwi_bc : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xbc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0xbc)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xbc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  (* 0xbe  64a2  ld s1,8(sp) *)
  Lemma lwi_be : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xbe) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.log_write + 0xbe)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xbe) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  (* 0xc0  6105  addi sp,sp,32 *)
  Lemma lwi_c0 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xc0) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.log_write + 0xc0)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xc0) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  (* 0xc2  8082  ret *)
  Lemma lwi_c2 : kernel_text -∗ instr (mword_of_int (KernelSyms.log_write + 0xc2) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.log_write + 0xc2)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.log_write + 0xc2) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End LogWriteInstrs.

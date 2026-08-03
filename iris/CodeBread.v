(* CodeBread.v -- the instruction-DECODE layer for xv6's bread().
   For EVERY instruction of

     bread @ 0x80002b36 .. 0x80002c0a   (offsets 0x00 .. 0xd4, 214 bytes)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([bdi_<off>]) plus
   the per-instruction decode facts they consume ([bddc_<word>] compressed /
   [bddb_<word>] base / [bdcx_<word>] the compressed leaf expansions).

   bget() is [static] with bread its only caller, so gcc INLINED it: this one
   function contains the forward hit scan, the backward LRU recycle scan, the
   "bget: no buffers" panic, both critical sections and the valid/read tail.
   Byte-exact disassembly (from the tracked kernel-rocq/KernelInstrs.v, NOT
   xv6-riscv/kernel/kernel.asm, which has drifted):

     0x00 7179       c.addi16sp sp,-48
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 ec26       c.sdsp s1,24(sp)
     0x08 e84a       c.sdsp s2,16(sp)
     0x0a e44e       c.sdsp s3,8(sp)
     0x0c 1800       c.addi4spn s0,sp,48
     0x0e 892a       c.mv  s2,a0            # s2 := dev
     0x10 89ae       c.mv  s3,a1            # s3 := blockno
     0x12 00015517   auipc a0,0x15
     0x16 64850513   addi  a0,a0,1608       # a0 := &bcache
     0x1a 8b8fe0ef   jal   ra,acquire
     0x1e 0001e497   auipc s1,0x1e
     0x22 8f44b483   ld    s1,-1804(s1)     # s1 := bcache.head.next
     0x26 0001e797   auipc a5,0x1e
     0x2a 89c78793   addi  a5,a5,-1892      # a5 := &bcache.head
     0x2e 02f48b63   beq   s1,a5,+0x36      # empty forward scan -> miss scan
     0x32 873e       c.mv  a4,a5            # a4 := the sentinel
     0x34 a021       c.j   +0x8             # -> the loop TEST at +0x3c
     0x36 68a4       c.ld  s1,80(s1)        # s1 := s1->next        (BACK EDGE)
     0x38 02e48663   beq   s1,a4,+0x2c      # wrapped -> miss scan
     0x3c 449c       c.lw  a5,8(s1)         # a5 := s1->dev
     0x3e ff279ce3   bne   a5,s2,-0x8       # dev mismatch -> advance
     0x42 44dc       c.lw  a5,12(s1)        # a5 := s1->blockno
     0x44 ff3799e3   bne   a5,s3,-0xe       # blockno mismatch -> advance
     0x48 40bc       c.lw  a5,64(s1)        # ---- HIT: refcnt++ ----
     0x4a 2785       c.addiw a5,a5,1
     0x4c c0bc       c.sw  a5,64(s1)
     0x4e 00015517   auipc a0,0x15
     0x52 60c50513   addi  a0,a0,1548       # a0 := &bcache
     0x56 904fe0ef   jal   ra,release
     0x5a 01048513   addi  a0,s1,16         # a0 := &b->lock
     0x5e 338010ef   jal   ra,acquiresleep
     0x62 a889       c.j   +0x52            # -> the TAIL at +0xb4
     0x64 0001e497   auipc s1,0x1e
     0x68 8a64b483   ld    s1,-1882(s1)     # s1 := bcache.head.prev
     0x6c 0001e797   auipc a5,0x1e
     0x70 85678793   addi  a5,a5,-1962      # a5 := &bcache.head
     0x74 00f48863   beq   s1,a5,+0x10      # empty -> panic
     0x78 873e       c.mv  a4,a5
     0x7a 40bc       c.lw  a5,64(s1)        # a5 := s1->refcnt      (BACK EDGE)
     0x7c cb91       c.beqz a5,+0x14        # refcnt == 0 -> recycle
     0x7e 64a4       c.ld  s1,72(s1)        # s1 := s1->prev
     0x80 fee49de3   bne   s1,a4,-0x6       # not wrapped -> retest
     0x84 00004517   auipc a0,0x4
     0x88 7e650513   addi  a0,a0,2022       # a0 := "bget: no buffers"
     0x8c c65fd0ef   jal   ra,panic
     0x90 0124a423   sw    s2,8(s1)         # ---- RECYCLE ----  b->dev = dev
     0x94 0134a623   sw    s3,12(s1)        # b->blockno = blockno
     0x98 0004a023   sw    zero,0(s1)       # b->valid = 0
     0x9c 4785       c.li  a5,1
     0x9e c0bc       c.sw  a5,64(s1)        # b->refcnt = 1
     0xa0 00015517   auipc a0,0x15
     0xa4 5ba50513   addi  a0,a0,1466       # a0 := &bcache
     0xa8 8b2fe0ef   jal   ra,release
     0xac 01048513   addi  a0,s1,16
     0xb0 2e6010ef   jal   ra,acquiresleep
     0xb4 409c       c.lw  a5,0(s1)         # ---- TAIL ----  a5 := b->valid
     0xb6 cb89       c.beqz a5,+0x12        # !valid -> the disk read
     0xb8 8526       c.mv  a0,s1            # ---- EPILOGUE ----
     0xba 70a2       c.ldsp ra,40(sp)
     0xbc 7402       c.ldsp s0,32(sp)
     0xbe 64e2       c.ldsp s1,24(sp)
     0xc0 6942       c.ldsp s2,16(sp)
     0xc2 69a2       c.ldsp s3,8(sp)
     0xc4 6145       c.addi16sp sp,48
     0xc6 8082       c.ret
     0xc8 4581       c.li  a1,0             # ---- READ ----  write = 0
     0xca 8526       c.mv  a0,s1
     0xcc 34f020ef   jal   ra,virtio_disk_rw
     0xd0 4785       c.li  a5,1
     0xd2 c09c       c.sw  a5,0(s1)         # b->valid = 1
     0xd4 b7d5       c.j   -0x1c            # -> the EPILOGUE at +0xb8

   SHARED WORDS.  Eleven of bread's words occur in other functions too, so
   they are NOT proved here -- they come from the two mid-tree decode bases
   (the dedup rule in claude-notes/durable-notes.md):
     * KernelRvcDecode.v: 0x40bc / 0xc0bc (the refcnt read/write, with their
       leaf-form expansions [cexec_40bc] / [cexec_c0bc]; also bpin, bunpin,
       brelse), 0xc09c (also initsleeplock / releasesleep), 0xcb91 (also
       allocproc, uartputc_sync), 0xa021 (also copyout, uvmcopy), 0x89ae
       (also walk), plus the frame words 0x8526 / 0x409c / 0x4581 / 0x8082.
     * KernelBaseDecode.v: 0x0001e497 (FIVE functions reach the 0x8002xxxx
       globals through it), 0x0001e797, 0x01048513 (also binit), 0x0004a023
       (also release / initsleeplock / releasesleep), 0x8b8fe0ef (also binit).
   Everything else here is bread's alone.                                    *)
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
(* Compressed decode facts private to bread.                              *)
(* ===================================================================== *)

(* 0x873e  c.mv a4,a5 -- the scan sentinel is copied into a4 (both scans) *)
Lemma bddc_873e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x873e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa889  c.j +0x52 -- the hit path jumps to the shared tail *)
Lemma bddc_a889 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa889 : mword 16)) s
  = Some (C_J (mword_of_int 41 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x68a4  c.ld s1,80(s1) -- the forward scan's [b = b->next] *)
Lemma bddc_68a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x68a4 : mword 16)) s
  = Some (C_LD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64a4  c.ld s1,72(s1) -- the backward scan's [b = b->prev] *)
Lemma bddc_64a4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x64a4 : mword 16)) s
  = Some (C_LD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x449c  c.lw a5,8(s1) -- [b->dev] *)
Lemma bddc_449c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x449c : mword 16)) s
  = Some (C_LW (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44dc  c.lw a5,12(s1) -- [b->blockno] *)
Lemma bddc_44dc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x44dc : mword 16)) s
  = Some (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xcb89  c.beqz a5,+0x12 -- !b->valid, take the disk read *)
Lemma bddc_cb89 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcb89 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 9, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- their leaf-form expansions: a literal [mword 12] displacement and
   plain [Regidx]es, which is the shape the WP load/store leaves take. ---- *)

Lemma bdcx_68a4 s :
  exec (execute (C_LD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bdcx_64a4 s :
  exec (execute (C_LD (mword_of_int 9, Cregidx (mword_of_int 1), Cregidx (mword_of_int 1)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bdcx_449c s :
  exec (execute (C_LW (mword_of_int 2, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bdcx_44dc s :
  exec (execute (C_LW (mword_of_int 3, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bdcx_409c s :
  exec (execute (C_LW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)), s).
Proof. apply exec_execute_C_LW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma bdcx_c09c s :
  exec (execute (C_SW (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* the three [addi a0,a0,<imm>] that materialize &bcache off the three auipcs *)
Lemma bddb_64850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x64850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_60c50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x60c50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1548 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_5ba50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5ba50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 1466 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_00004517 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00004517 : mword 32)) s
  = Some (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* ld s1,-1804(s1) / ld s1,-1882(s1): bcache.head.next / bcache.head.prev.
   The decoder's immediates are the POSITIVE RESIDUES mod 2^12. *)
Lemma bddb_8f44b483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8f44b483 : mword 32)) s
  = Some (LOAD (mword_of_int 2292 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_8a64b483 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8a64b483 : mword 32)) s
  = Some (LOAD (mword_of_int 2214 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* addi a5,a5,-1892 / addi a5,a5,-1962 -- the sentinel &bcache.head *)
Lemma bddb_89c78793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x89c78793 : mword 32)) s
  = Some (ITYPE (mword_of_int 2204 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_85678793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x85678793 : mword 32)) s
  = Some (ITYPE (mword_of_int 2134 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* addi a0,a0,2022 -- the panic string "bget: no buffers" @ 0x800073a0 *)
Lemma bddb_7e650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7e650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 2022 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* the four branches of the two scans *)
Lemma bddb_02f48b63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f48b63 : mword 32)) s
  = Some (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_02e48663 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02e48663 : mword 32)) s
  = Some (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_ff279ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff279ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_ff3799e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff3799e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8178 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_00f48863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f48863 : mword 32)) s
  = Some (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_fee49de3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfee49de3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8186 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* the three field stores of the recycle block *)
Lemma bddb_0124a423 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0124a423 : mword 32)) s
  = Some (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_0134a623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0134a623 : mword 32)) s
  = Some (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_904fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x904fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089220 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_8b2fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8b2fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089138 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_338010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x338010ef : mword 32)) s
  = Some (JAL (mword_of_int 4920 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_2e6010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2e6010ef : mword 32)) s
  = Some (JAL (mword_of_int 4838 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_c65fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc65fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088036 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bddb_34f020ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x34f020ef : mword 32)) s
  = Some (JAL (mword_of_int 11086 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BreadInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation BD := KernelSyms.bread.

  (* ---- prologue ---- *)
  Lemma bdi_00 : kernel_text -∗ instr (mword_of_int (BD + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BD + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (BD + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma bdi_02 : kernel_text -∗ instr (mword_of_int (BD + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BD + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (BD + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma bdi_04 : kernel_text -∗ instr (mword_of_int (BD + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BD + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (BD + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma bdi_06 : kernel_text -∗ instr (mword_of_int (BD + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BD + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (BD + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma bdi_08 : kernel_text -∗ instr (mword_of_int (BD + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (BD + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (BD + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma bdi_0a : kernel_text -∗ instr (mword_of_int (BD + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (BD + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (BD + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma bdi_0c : kernel_text -∗ instr (mword_of_int (BD + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BD + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (BD + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma bdi_0e : kernel_text -∗ instr (mword_of_int (BD + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (BD + 0x0e)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (BD + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma bdi_10 : kernel_text -∗ instr (mword_of_int (BD + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (BD + 0x10)%Z (mword_of_int 0x89ae : mword 16)
    (mword_of_int (BD + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 19), ADD)) cdec_89ae exec_execute_C_MV. Qed.

  (* ---- acquire(&bcache.lock) ---- *)
  Lemma bdi_12 : kernel_text -∗ instr (mword_of_int (BD + 0x12) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BD + 0x12)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BD + 0x12) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bdi_16 : kernel_text -∗ instr (mword_of_int (BD + 0x16) : mword 64) false (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0x16)%Z (mword_of_int 0x64850513 : mword 32)
    (mword_of_int (BD + 0x16) : mword 64) (ITYPE (mword_of_int 1608 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bddb_64850513. Qed.

  Lemma bdi_1a : kernel_text -∗ instr (mword_of_int (BD + 0x1a) : mword 64) false (JAL (mword_of_int 2089144 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0x1a)%Z (mword_of_int 0x8b8fe0ef : mword 32)
    (mword_of_int (BD + 0x1a) : mword 64) (JAL (mword_of_int 2089144 : mword 21, Regidx (mword_of_int 1))) bdec_8b8fe0ef. Qed.

  (* ---- the forward (hit) scan ---- *)
  Lemma bdi_1e : kernel_text -∗ instr (mword_of_int (BD + 0x1e) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (BD + 0x1e)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (BD + 0x1e) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  Lemma bdi_22 : kernel_text -∗ instr (mword_of_int (BD + 0x22) : mword 64) false (LOAD (mword_of_int 2292 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_base (BD + 0x22)%Z (mword_of_int 0x8f44b483 : mword 32)
    (mword_of_int (BD + 0x22) : mword 64) (LOAD (mword_of_int 2292 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)) bddb_8f44b483. Qed.

  Lemma bdi_26 : kernel_text -∗ instr (mword_of_int (BD + 0x26) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (BD + 0x26)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (BD + 0x26) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  Lemma bdi_2a : kernel_text -∗ instr (mword_of_int (BD + 0x2a) : mword 64) false (ITYPE (mword_of_int 2204 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (BD + 0x2a)%Z (mword_of_int 0x89c78793 : mword 32)
    (mword_of_int (BD + 0x2a) : mword 64) (ITYPE (mword_of_int 2204 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bddb_89c78793. Qed.

  Lemma bdi_2e : kernel_text -∗ instr (mword_of_int (BD + 0x2e) : mword 64) false (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (BD + 0x2e)%Z (mword_of_int 0x02f48b63 : mword 32)
    (mword_of_int (BD + 0x2e) : mword 64) (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ)) bddb_02f48b63. Qed.

  Lemma bdi_32 : kernel_text -∗ instr (mword_of_int (BD + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (BD + 0x32)%Z (mword_of_int 0x873e : mword 16)
    (mword_of_int (BD + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)) bddc_873e exec_execute_C_MV. Qed.

  Lemma bdi_34 : kernel_text -∗ instr (mword_of_int (BD + 0x34) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BD + 0x34)%Z (mword_of_int 0xa021 : mword 16)
    (mword_of_int (BD + 0x34) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)) cdec_a021 exec_execute_C_J. Qed.

  Lemma bdi_36 : kernel_text -∗ instr (mword_of_int (BD + 0x36) : mword 64) true (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BD + 0x36)%Z (mword_of_int 0x68a4 : mword 16)
    (mword_of_int (BD + 0x36) : mword 64) (LOAD (mword_of_int 80, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)) bddc_68a4 bdcx_68a4. Qed.

  Lemma bdi_38 : kernel_text -∗ instr (mword_of_int (BD + 0x38) : mword 64) false (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (BD + 0x38)%Z (mword_of_int 0x02e48663 : mword 32)
    (mword_of_int (BD + 0x38) : mword 64) (BTYPE (mword_of_int 44 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BEQ)) bddb_02e48663. Qed.

  Lemma bdi_3c : kernel_text -∗ instr (mword_of_int (BD + 0x3c) : mword 64) true (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BD + 0x3c)%Z (mword_of_int 0x449c : mword 16)
    (mword_of_int (BD + 0x3c) : mword 64) (LOAD (mword_of_int 8, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bddc_449c bdcx_449c. Qed.

  Lemma bdi_3e : kernel_text -∗ instr (mword_of_int (BD + 0x3e) : mword 64) false (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (BD + 0x3e)%Z (mword_of_int 0xff279ce3 : mword 32)
    (mword_of_int (BD + 0x3e) : mword 64) (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 15), BNE)) bddb_ff279ce3. Qed.

  Lemma bdi_42 : kernel_text -∗ instr (mword_of_int (BD + 0x42) : mword 64) true (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BD + 0x42)%Z (mword_of_int 0x44dc : mword 16)
    (mword_of_int (BD + 0x42) : mword 64) (LOAD (mword_of_int 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bddc_44dc bdcx_44dc. Qed.

  Lemma bdi_44 : kernel_text -∗ instr (mword_of_int (BD + 0x44) : mword 64) false (BTYPE (mword_of_int 8178 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (BD + 0x44)%Z (mword_of_int 0xff3799e3 : mword 32)
    (mword_of_int (BD + 0x44) : mword 64) (BTYPE (mword_of_int 8178 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)) bddb_ff3799e3. Qed.

  (* ---- the HIT: refcnt++, release, acquiresleep ---- *)
  Lemma bdi_48 : kernel_text -∗ instr (mword_of_int (BD + 0x48) : mword 64) true (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BD + 0x48)%Z (mword_of_int 0x40bc : mword 16)
    (mword_of_int (BD + 0x48) : mword 64) (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40bc cexec_40bc. Qed.

  Lemma bdi_4a : kernel_text -∗ instr (mword_of_int (BD + 0x4a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (BD + 0x4a)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (BD + 0x4a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma bdi_4c : kernel_text -∗ instr (mword_of_int (BD + 0x4c) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (BD + 0x4c)%Z (mword_of_int 0xc0bc : mword 16)
    (mword_of_int (BD + 0x4c) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0bc cexec_c0bc. Qed.

  Lemma bdi_4e : kernel_text -∗ instr (mword_of_int (BD + 0x4e) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BD + 0x4e)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BD + 0x4e) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bdi_52 : kernel_text -∗ instr (mword_of_int (BD + 0x52) : mword 64) false (ITYPE (mword_of_int 1548 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0x52)%Z (mword_of_int 0x60c50513 : mword 32)
    (mword_of_int (BD + 0x52) : mword 64) (ITYPE (mword_of_int 1548 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bddb_60c50513. Qed.

  Lemma bdi_56 : kernel_text -∗ instr (mword_of_int (BD + 0x56) : mword 64) false (JAL (mword_of_int 2089220 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0x56)%Z (mword_of_int 0x904fe0ef : mword 32)
    (mword_of_int (BD + 0x56) : mword 64) (JAL (mword_of_int 2089220 : mword 21, Regidx (mword_of_int 1))) bddb_904fe0ef. Qed.

  Lemma bdi_5a : kernel_text -∗ instr (mword_of_int (BD + 0x5a) : mword 64) false (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0x5a)%Z (mword_of_int 0x01048513 : mword 32)
    (mword_of_int (BD + 0x5a) : mword 64) (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_01048513. Qed.

  Lemma bdi_5e : kernel_text -∗ instr (mword_of_int (BD + 0x5e) : mword 64) false (JAL (mword_of_int 4920 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0x5e)%Z (mword_of_int 0x338010ef : mword 32)
    (mword_of_int (BD + 0x5e) : mword 64) (JAL (mword_of_int 4920 : mword 21, Regidx (mword_of_int 1))) bddb_338010ef. Qed.

  Lemma bdi_62 : kernel_text -∗ instr (mword_of_int (BD + 0x62) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 41 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BD + 0x62)%Z (mword_of_int 0xa889 : mword 16)
    (mword_of_int (BD + 0x62) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 41 : mword 11) ('b"0")), zreg)) bddc_a889 exec_execute_C_J. Qed.

  (* ---- the backward (miss) scan ---- *)
  Lemma bdi_64 : kernel_text -∗ instr (mword_of_int (BD + 0x64) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (BD + 0x64)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (BD + 0x64) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  Lemma bdi_68 : kernel_text -∗ instr (mword_of_int (BD + 0x68) : mword 64) false (LOAD (mword_of_int 2214 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_base (BD + 0x68)%Z (mword_of_int 0x8a64b483 : mword 32)
    (mword_of_int (BD + 0x68) : mword 64) (LOAD (mword_of_int 2214 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)) bddb_8a64b483. Qed.

  Lemma bdi_6c : kernel_text -∗ instr (mword_of_int (BD + 0x6c) : mword 64) false (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (BD + 0x6c)%Z (mword_of_int 0x0001e797 : mword 32)
    (mword_of_int (BD + 0x6c) : mword 64) (UTYPE (mword_of_int 30 : mword 20, Regidx (mword_of_int 15), AUIPC)) bdec_0001e797. Qed.

  Lemma bdi_70 : kernel_text -∗ instr (mword_of_int (BD + 0x70) : mword 64) false (ITYPE (mword_of_int 2134 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (BD + 0x70)%Z (mword_of_int 0x85678793 : mword 32)
    (mword_of_int (BD + 0x70) : mword 64) (ITYPE (mword_of_int 2134 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bddb_85678793. Qed.

  Lemma bdi_74 : kernel_text -∗ instr (mword_of_int (BD + 0x74) : mword 64) false (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (BD + 0x74)%Z (mword_of_int 0x00f48863 : mword 32)
    (mword_of_int (BD + 0x74) : mword 64) (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 9), BEQ)) bddb_00f48863. Qed.

  Lemma bdi_78 : kernel_text -∗ instr (mword_of_int (BD + 0x78) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (BD + 0x78)%Z (mword_of_int 0x873e : mword 16)
    (mword_of_int (BD + 0x78) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 14), ADD)) bddc_873e exec_execute_C_MV. Qed.

  Lemma bdi_7a : kernel_text -∗ instr (mword_of_int (BD + 0x7a) : mword 64) true (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BD + 0x7a)%Z (mword_of_int 0x40bc : mword 16)
    (mword_of_int (BD + 0x7a) : mword 64) (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40bc cexec_40bc. Qed.

  Lemma bdi_7c : kernel_text -∗ instr (mword_of_int (BD + 0x7c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (BD + 0x7c)%Z (mword_of_int 0xcb91 : mword 16)
    (mword_of_int (BD + 0x7c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_cb91 exec_execute_C_BEQZ. Qed.

  Lemma bdi_7e : kernel_text -∗ instr (mword_of_int (BD + 0x7e) : mword 64) true (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BD + 0x7e)%Z (mword_of_int 0x64a4 : mword 16)
    (mword_of_int (BD + 0x7e) : mword 64) (LOAD (mword_of_int 72, Regidx (mword_of_int 9), Regidx (mword_of_int 9), false, 8)) bddc_64a4 bdcx_64a4. Qed.

  Lemma bdi_80 : kernel_text -∗ instr (mword_of_int (BD + 0x80) : mword 64) false (BTYPE (mword_of_int 8186 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (BD + 0x80)%Z (mword_of_int 0xfee49de3 : mword 32)
    (mword_of_int (BD + 0x80) : mword 64) (BTYPE (mword_of_int 8186 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE)) bddb_fee49de3. Qed.

  (* ---- the panic arm ("bget: no buffers") ---- *)
  Lemma bdi_84 : kernel_text -∗ instr (mword_of_int (BD + 0x84) : mword 64) false (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BD + 0x84)%Z (mword_of_int 0x00004517 : mword 32)
    (mword_of_int (BD + 0x84) : mword 64) (UTYPE (mword_of_int 4 : mword 20, Regidx (mword_of_int 10), AUIPC)) bddb_00004517. Qed.

  Lemma bdi_88 : kernel_text -∗ instr (mword_of_int (BD + 0x88) : mword 64) false (ITYPE (mword_of_int 2022 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0x88)%Z (mword_of_int 0x7e650513 : mword 32)
    (mword_of_int (BD + 0x88) : mword 64) (ITYPE (mword_of_int 2022 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bddb_7e650513. Qed.

  Lemma bdi_8c : kernel_text -∗ instr (mword_of_int (BD + 0x8c) : mword 64) false (JAL (mword_of_int 2088036 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0x8c)%Z (mword_of_int 0xc65fd0ef : mword 32)
    (mword_of_int (BD + 0x8c) : mword 64) (JAL (mword_of_int 2088036 : mword 21, Regidx (mword_of_int 1))) bddb_c65fd0ef. Qed.

  (* ---- the RECYCLE block ---- *)
  Lemma bdi_90 : kernel_text -∗ instr (mword_of_int (BD + 0x90) : mword 64) false (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (BD + 0x90)%Z (mword_of_int 0x0124a423 : mword 32)
    (mword_of_int (BD + 0x90) : mword 64) (STORE (mword_of_int 8 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 9), 4)) bddb_0124a423. Qed.

  Lemma bdi_94 : kernel_text -∗ instr (mword_of_int (BD + 0x94) : mword 64) false (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (BD + 0x94)%Z (mword_of_int 0x0134a623 : mword 32)
    (mword_of_int (BD + 0x94) : mword 64) (STORE (mword_of_int 12 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 9), 4)) bddb_0134a623. Qed.

  Lemma bdi_98 : kernel_text -∗ instr (mword_of_int (BD + 0x98) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (BD + 0x98)%Z (mword_of_int 0x0004a023 : mword 32)
    (mword_of_int (BD + 0x98) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) bdec_0004a023. Qed.

  Lemma bdi_9c : kernel_text -∗ instr (mword_of_int (BD + 0x9c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (BD + 0x9c)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (BD + 0x9c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma bdi_9e : kernel_text -∗ instr (mword_of_int (BD + 0x9e) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (BD + 0x9e)%Z (mword_of_int 0xc0bc : mword 16)
    (mword_of_int (BD + 0x9e) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0bc cexec_c0bc. Qed.

  Lemma bdi_a0 : kernel_text -∗ instr (mword_of_int (BD + 0xa0) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BD + 0xa0)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BD + 0xa0) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bdi_a4 : kernel_text -∗ instr (mword_of_int (BD + 0xa4) : mword 64) false (ITYPE (mword_of_int 1466 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0xa4)%Z (mword_of_int 0x5ba50513 : mword 32)
    (mword_of_int (BD + 0xa4) : mword 64) (ITYPE (mword_of_int 1466 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bddb_5ba50513. Qed.

  Lemma bdi_a8 : kernel_text -∗ instr (mword_of_int (BD + 0xa8) : mword 64) false (JAL (mword_of_int 2089138 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0xa8)%Z (mword_of_int 0x8b2fe0ef : mword 32)
    (mword_of_int (BD + 0xa8) : mword 64) (JAL (mword_of_int 2089138 : mword 21, Regidx (mword_of_int 1))) bddb_8b2fe0ef. Qed.

  Lemma bdi_ac : kernel_text -∗ instr (mword_of_int (BD + 0xac) : mword 64) false (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BD + 0xac)%Z (mword_of_int 0x01048513 : mword 32)
    (mword_of_int (BD + 0xac) : mword 64) (ITYPE (mword_of_int 16 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_01048513. Qed.

  Lemma bdi_b0 : kernel_text -∗ instr (mword_of_int (BD + 0xb0) : mword 64) false (JAL (mword_of_int 4838 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0xb0)%Z (mword_of_int 0x2e6010ef : mword 32)
    (mword_of_int (BD + 0xb0) : mword 64) (JAL (mword_of_int 4838 : mword 21, Regidx (mword_of_int 1))) bddb_2e6010ef. Qed.

  (* ---- the shared TAIL and the two epilogue arms ---- *)
  Lemma bdi_b4 : kernel_text -∗ instr (mword_of_int (BD + 0xb4) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BD + 0xb4)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (BD + 0xb4) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_409c bdcx_409c. Qed.

  Lemma bdi_b6 : kernel_text -∗ instr (mword_of_int (BD + 0xb6) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (BD + 0xb6)%Z (mword_of_int 0xcb89 : mword 16)
    (mword_of_int (BD + 0xb6) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) bddc_cb89 exec_execute_C_BEQZ. Qed.

  Lemma bdi_b8 : kernel_text -∗ instr (mword_of_int (BD + 0xb8) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BD + 0xb8)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (BD + 0xb8) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma bdi_ba : kernel_text -∗ instr (mword_of_int (BD + 0xba) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BD + 0xba)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (BD + 0xba) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma bdi_bc : kernel_text -∗ instr (mword_of_int (BD + 0xbc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BD + 0xbc)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (BD + 0xbc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma bdi_be : kernel_text -∗ instr (mword_of_int (BD + 0xbe) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BD + 0xbe)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (BD + 0xbe) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma bdi_c0 : kernel_text -∗ instr (mword_of_int (BD + 0xc0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (BD + 0xc0)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (BD + 0xc0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma bdi_c2 : kernel_text -∗ instr (mword_of_int (BD + 0xc2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (BD + 0xc2)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (BD + 0xc2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma bdi_c4 : kernel_text -∗ instr (mword_of_int (BD + 0xc4) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BD + 0xc4)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (BD + 0xc4) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma bdi_c6 : kernel_text -∗ instr (mword_of_int (BD + 0xc6) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BD + 0xc6)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BD + 0xc6) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- the disk-read arm ---- *)
  Lemma bdi_c8 : kernel_text -∗ instr (mword_of_int (BD + 0xc8) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (BD + 0xc8)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (BD + 0xc8) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma bdi_ca : kernel_text -∗ instr (mword_of_int (BD + 0xca) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (BD + 0xca)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (BD + 0xca) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma bdi_cc : kernel_text -∗ instr (mword_of_int (BD + 0xcc) : mword 64) false (JAL (mword_of_int 11086 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BD + 0xcc)%Z (mword_of_int 0x34f020ef : mword 32)
    (mword_of_int (BD + 0xcc) : mword 64) (JAL (mword_of_int 11086 : mword 21, Regidx (mword_of_int 1))) bddb_34f020ef. Qed.

  Lemma bdi_d0 : kernel_text -∗ instr (mword_of_int (BD + 0xd0) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (BD + 0xd0)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (BD + 0xd0) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma bdi_d2 : kernel_text -∗ instr (mword_of_int (BD + 0xd2) : mword 64) true (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (BD + 0xd2)%Z (mword_of_int 0xc09c : mword 16)
    (mword_of_int (BD + 0xd2) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c09c bdcx_c09c. Qed.

  Lemma bdi_d4 : kernel_text -∗ instr (mword_of_int (BD + 0xd4) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (BD + 0xd4)%Z (mword_of_int 0xb7d5 : mword 16)
    (mword_of_int (BD + 0xd4) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)) cdec_b7d5 exec_execute_C_J. Qed.

End BreadInstrs.

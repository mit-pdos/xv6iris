(* CodeUvmcopy.v -- the instruction-DECODE layer for xv6's uvmcopy().

     uvmcopy @ 0x80001404 .. 0x8000149d   (offsets 0x00 .. 0x98, 65 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([uci_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the twelve 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; uvmcopy's own words are local, named [ucdc_<word>]
   (compressed) / [ucdb_<word>] (base).

     int uvmcopy(pagetable_t old /*a0*/, pagetable_t new /*a1*/,
                 uint64 sz /*a2*/)

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- the .asm listing has drifted by 0xe bytes):

     0x00 ca59        c.beqz a2,+0x96           # sz == 0 -> 0x96, NO frame
     0x02 715d        c.addi16sp sp,-80         # 80-byte frame (10 slots)
     0x04 e486        c.sdsp ra,72(sp)
     0x06 e0a2        c.sdsp s0,64(sp)
     0x08 fc26        c.sdsp s1,56(sp)
     0x0a f84a        c.sdsp s2,48(sp)
     0x0c f44e        c.sdsp s3,40(sp)
     0x0e f052        c.sdsp s4,32(sp)
     0x10 ec56        c.sdsp s5,24(sp)
     0x12 e85a        c.sdsp s6,16(sp)
     0x14 e45e        c.sdsp s7,8(sp)
     0x16 0880        c.addi4spn s0,sp,80
     0x18 8b2a        c.mv   s6,a0              # s6 := old
     0x1a 8bae        c.mv   s7,a1              # s7 := new
     0x1c 8ab2        c.mv   s5,a2              # s5 := sz
     0x1e 4481        c.li   s1,0               # s1 := i
     0x20 6a05        c.lui  s4,0x1             # s4 := PGSIZE
     0x22 a021        c.j    +0x08              # -> 0x2a, enter the loop
     0x24 94d2        c.add  s1,s1,s4           # i += PGSIZE   <- back edge
     0x26 0554fc63    bgeu  s1,s5,+0x58         # -> 0x7e, loop done, return 0
     0x2a 4601        c.li   a2,0               # walk(old, i, 0)  <- loop head
     0x2c 85a6        c.mv   a1,s1
     0x2e 855a        c.mv   a0,s6
     0x30 b29ff0ef    jal   ra,walk             # 0x80000f5c
     0x34 d965        c.beqz a0,-0x10           # -> 0x24, no pte: skip
     0x36 00053983    ld    s3,0(a0)            # s3 := *pte
     0x3a 0019f793    andi  a5,s3,1             # PTE_V
     0x3e d3fd        c.beqz a5,-0x1a           # -> 0x24, not valid: skip
     0x40 eeaff0ef    jal   ra,kalloc           # 0x80000b2e
     0x44 892a        c.mv   s2,a0              # s2 := mem
     0x46 c11d        c.beqz a0,+0x26           # -> 0x6c, out of memory
     0x48 00a9d593    srli  a1,s3,0xa           # PTE2PA( *pte ) ...
     0x4c 8652        c.mv   a2,s4              # PGSIZE
     0x4e 05b2        c.slli a1,a1,0xc          # ... << 12
     0x50 8d5ff0ef    jal   ra,memmove          # 0x80000d28
     0x54 3ff9f713    andi  a4,s3,1023          # flags := PTE_FLAGS( *pte )
     0x58 86ca        c.mv   a3,s2              # mem
     0x5a 8652        c.mv   a2,s4              # PGSIZE
     0x5c 85a6        c.mv   a1,s1              # i
     0x5e 855e        c.mv   a0,s7              # new
     0x60 bcdff0ef    jal   ra,mappages         # 0x80001030
     0x64 d161        c.beqz a0,-0x40           # -> 0x24, mapped ok: next page
     0x66 854a        c.mv   a0,s2              # --- mappages failed
     0x68 ddaff0ef    jal   ra,kfree            # 0x80000a46
     0x6c 4685        c.li   a3,1               # --- the error exit
     0x6e 00c4d613    srli  a2,s1,0xc           # i / PGSIZE pages
     0x72 4581        c.li   a1,0
     0x74 855e        c.mv   a0,s7
     0x76 d85ff0ef    jal   ra,uvmunmap         # 0x800011fe
     0x7a 557d        c.li   a0,-1              # return -1
     0x7c a011        c.j    +0x04              # -> 0x80
     0x7e 4501        c.li   a0,0               # --- success: return 0
     0x80 60a6        c.ldsp ra,72(sp)          # --- the common epilogue
     0x82 6406        c.ldsp s0,64(sp)
     0x84 74e2        c.ldsp s1,56(sp)
     0x86 7942        c.ldsp s2,48(sp)
     0x88 79a2        c.ldsp s3,40(sp)
     0x8a 7a02        c.ldsp s4,32(sp)
     0x8c 6ae2        c.ldsp s5,24(sp)
     0x8e 6b42        c.ldsp s6,16(sp)
     0x90 6ba2        c.ldsp s7,8(sp)
     0x92 6161        c.addi16sp sp,80
     0x94 8082        c.ret
     0x96 4501        c.li   a0,0               # --- sz == 0: frameless exit
     0x98 8082        c.ret

   Two structural oddities worth flagging for the WP layer above:

     * the FIRST instruction is the compressed [c.beqz a2,+0x96], taken
       BEFORE the frame is pushed, so the 0x96..0x98 arm returns 0 with sp
       untouched and never reaches the common epilogue at 0x80;
     * unlike uvmalloc there is no shrink-wrapping here: all nine callee-saved
       registers are pushed in one block at 0x04..0x14 and popped in one block
       at 0x80..0x90, and BOTH the success arm (0x7e) and the error arm
       (0x7a..0x7c) fall into that single epilogue.

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.beqz]s are 248 / 243 / 224 (2^8 complements of -8 / -13 / -32
   half-words) and the [bgeu] at 0x26 is a plain +88 bytes; the six [jal]s are
   2095912 / 2094826 / 2095316 / 2096076 / 2094554 / 2096516 (2^21 complements
   of -1240 / -2326 / -1836 / -1076 / -2598 / -636 bytes).  For BTYPE/JAL the
   AST arg is the BYTE offset residue; for C_J / C_BEQZ / C_BNEZ it is the
   offset/2 residue, re-widened by the [concat_vec ... 'b"0"] in the [instr]
   fact.                                                                    *)
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
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for uvmcopy's own words.                       *)
(*                                                                        *)
(* Reused straight from KernelRvcDecode.v (no local copy needed):         *)
(*   0x02 c.addi16sp sp,-80      [cdec_715d]                              *)
(*   0x04 c.sdsp ra,72(sp)       [cdec_e486]                              *)
(*   0x06 c.sdsp s0,64(sp)       [cdec_e0a2]                              *)
(*   0x08 c.sdsp s1,56(sp)       [cdec_fc26]                              *)
(*   0x0a c.sdsp s2,48(sp)       [cdec_f84a]                              *)
(*   0x0c c.sdsp s3,40(sp)       [cdec_f44e]                              *)
(*   0x0e c.sdsp s4,32(sp)       [cdec_f052]                              *)
(*   0x10 c.sdsp s5,24(sp)       [cdec_ec56]                              *)
(*   0x12 c.sdsp s6,16(sp)       [cdec_e85a]                              *)
(*   0x14 c.sdsp s7,8(sp)        [cdec_e45e]                              *)
(*   0x16 c.addi4spn s0,sp,80    [cdec_0880]                              *)
(*   0x2a c.li  a2,0             [cdec_4601]                              *)
(*   0x2c c.mv  a1,s1            [cdec_85a6]                              *)
(*   0x5c c.mv  a1,s1            [cdec_85a6]                              *)
(*   0x5e c.mv  a0,s7            [cdec_855e]                              *)
(*   0x66 c.mv  a0,s2            [cdec_854a]                              *)
(*   0x72 c.li  a1,0             [cdec_4581]                              *)
(*   0x74 c.mv  a0,s7            [cdec_855e]                              *)
(*   0x7a c.li  a0,-1            [cdec_557d]                              *)
(*   0x7e c.li  a0,0             [cdec_4501]                              *)
(*   0x80 c.ldsp ra,72(sp)       [cdec_60a6]                              *)
(*   0x82 c.ldsp s0,64(sp)       [cdec_6406]                              *)
(*   0x84 c.ldsp s1,56(sp)       [cdec_74e2]                              *)
(*   0x86 c.ldsp s2,48(sp)       [cdec_7942]                              *)
(*   0x88 c.ldsp s3,40(sp)       [cdec_79a2]                              *)
(*   0x8a c.ldsp s4,32(sp)       [cdec_7a02]                              *)
(*   0x8c c.ldsp s5,24(sp)       [cdec_6ae2]                              *)
(*   0x8e c.ldsp s6,16(sp)       [cdec_6b42]                              *)
(*   0x90 c.ldsp s7,8(sp)        [cdec_6ba2]                              *)
(*   0x92 c.addi16sp sp,80       [cdec_6161]                              *)
(*   0x94 c.ret                  [cdec_8082]                              *)
(*   0x96 c.li  a0,0             [cdec_4501]                              *)
(*   0x98 c.ret                  [cdec_8082]                              *)
(* ===================================================================== *)

(* 0x00  c.beqz a2,+0x96  -- the sz == 0 fast path (offset/2 = 75, rs1' = 4) *)
Lemma ucdc_ca59 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xca59 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 75, Cregidx (mword_of_int 4)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x18  c.mv s6,a0 *)
Lemma ucdc_8b2a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b2a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 22), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1a  c.mv s7,a1 *)
Lemma ucdc_8bae s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8bae : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 23), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1c  c.mv s5,a2 *)
Lemma ucdc_8ab2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8ab2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1e  c.li s1,0 *)
Lemma ucdc_4481 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4481 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x20  c.lui s4,0x1 *)
Lemma ucdc_6a05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a05 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x24  c.add s1,s4  -- i += PGSIZE *)
Lemma ucdc_94d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94d2 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_855a] (0x2e, c.mv a0,s6) -- shared, see KernelRvcDecode.v *)

(* 0x34  c.beqz a0,-0x10  (offset/2 = -8; 8-bit residue 248) *)
Lemma ucdc_d965 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd965 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 248, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x3e  c.beqz a5,-0x1a  (offset/2 = -13; 8-bit residue 243, rs1' = 7) *)
Lemma ucdc_d3fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd3fd : mword 16)) s
  = Some (C_BEQZ (mword_of_int 243, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x44  c.mv s2,a0 *)

(* 0x46  c.beqz a0,+0x26  (offset/2 = 19) *)
Lemma ucdc_c11d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc11d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 19, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4c / 0x5a  c.mv a2,s4 *)
Lemma ucdc_8652 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8652 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4e  c.slli a1,a1,0xc *)
Lemma ucdc_05b2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x05b2 : mword 16)) s
  = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x58  c.mv a3,s2 *)
Lemma ucdc_86ca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86ca : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64  c.beqz a0,-0x40  (offset/2 = -32; 8-bit residue 224) *)
Lemma ucdc_d161 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd161 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 224, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6c  c.li a3,1 *)
Lemma ucdc_4685 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4685 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7c  c.j +0x04  (offset/2 = 2) *)
Lemma ucdc_a011 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa011 : mword 16)) s
  = Some (C_J (mword_of_int 2), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all twelve are uvmcopy's own.            *)
(* ===================================================================== *)

(* 0x26  bgeu s1,s5,+0x58  -- loop exit to 0x7e (a plain positive 88) *)
Lemma ucdb_0554fc63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0554fc63 : mword 32)) s
  = Some (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x30  jal ra,walk       (0x80001434 -> 0x80000f5c is -1240) *)
Lemma ucdb_b29ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb29ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095912 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x36  ld s3,0(a0)  -- s3 := *pte *)
Lemma ucdb_00053983 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00053983 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x3a  andi a5,s3,1  -- the PTE_V test *)
Lemma ucdb_0019f793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0019f793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x40  jal ra,kalloc     (0x80001444 -> 0x80000b2e is -2326) *)
Lemma ucdb_eeaff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xeeaff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094826 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  srli a1,s3,0xa  -- PTE2PA( *pte ), first half *)
Lemma ucdb_00a9d593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00a9d593 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 19),
                    Regidx (mword_of_int 11), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x50  jal ra,memmove    (0x80001454 -> 0x80000d28 is -1836) *)
Lemma ucdb_8d5ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8d5ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095316 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x54  andi a4,s3,1023  -- flags := PTE_FLAGS( *pte ) *)
Lemma ucdb_3ff9f713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x3ff9f713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x60  jal ra,mappages   (0x80001464 -> 0x80001030 is -1076) *)
Lemma ucdb_bcdff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xbcdff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096076 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x68  jal ra,kfree      (0x8000146c -> 0x80000a46 is -2598) *)
Lemma ucdb_ddaff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xddaff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094554 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x6e  srli a2,s1,0xc  -- i / PGSIZE, the npages argument of uvmunmap *)
Lemma ucdb_00c4d613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c4d613 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9),
                    Regidx (mword_of_int 12), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x76  jal ra,uvmunmap   (0x8000147a -> 0x800011fe is -636) *)
Lemma ucdb_d85ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd85ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096516 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmcopyInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation UC := KernelSyms.uvmcopy.

  (* --- the frameless [sz == 0] fast path -------------------------------- *)

  Lemma uci_00 : kernel_text -∗ instr (mword_of_int (UC + 0x00) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 75 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)).
  Proof. mk_rvc (UC + 0x00)%Z (mword_of_int 0xca59 : mword 16)
    (mword_of_int (UC + 0x00) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 75 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 4)), BEQ)) ucdc_ca59 exec_execute_C_BEQZ. Qed.

  (* --- prologue: the 80-byte frame, all nine callee-saved regs ---------- *)

  Lemma uci_02 : kernel_text -∗ instr (mword_of_int (UC + 0x02) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UC + 0x02)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (UC + 0x02) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  Lemma uci_04 : kernel_text -∗ instr (mword_of_int (UC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UC + 0x04)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (UC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  Lemma uci_06 : kernel_text -∗ instr (mword_of_int (UC + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UC + 0x06)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (UC + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  Lemma uci_08 : kernel_text -∗ instr (mword_of_int (UC + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UC + 0x08)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (UC + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  Lemma uci_0a : kernel_text -∗ instr (mword_of_int (UC + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (UC + 0x0a)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (UC + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  Lemma uci_0c : kernel_text -∗ instr (mword_of_int (UC + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (UC + 0x0c)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (UC + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  Lemma uci_0e : kernel_text -∗ instr (mword_of_int (UC + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (UC + 0x0e)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (UC + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  Lemma uci_10 : kernel_text -∗ instr (mword_of_int (UC + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (UC + 0x10)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (UC + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  Lemma uci_12 : kernel_text -∗ instr (mword_of_int (UC + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (UC + 0x12)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (UC + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  Lemma uci_14 : kernel_text -∗ instr (mword_of_int (UC + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (UC + 0x14)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (UC + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  Lemma uci_16 : kernel_text -∗ instr (mword_of_int (UC + 0x16) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UC + 0x16)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (UC + 0x16) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  (* --- the arguments are parked in callee-saved regs -------------------- *)

  Lemma uci_18 : kernel_text -∗ instr (mword_of_int (UC + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (UC + 0x18)%Z (mword_of_int 0x8b2a : mword 16)
    (mword_of_int (UC + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 22), ADD)) ucdc_8b2a exec_execute_C_MV. Qed.

  Lemma uci_1a : kernel_text -∗ instr (mword_of_int (UC + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 23), ADD)).
  Proof. mk_rvc (UC + 0x1a)%Z (mword_of_int 0x8bae : mword 16)
    (mword_of_int (UC + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 23), ADD)) ucdc_8bae exec_execute_C_MV. Qed.

  Lemma uci_1c : kernel_text -∗ instr (mword_of_int (UC + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (UC + 0x1c)%Z (mword_of_int 0x8ab2 : mword 16)
    (mword_of_int (UC + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 21), ADD)) ucdc_8ab2 exec_execute_C_MV. Qed.

  Lemma uci_1e : kernel_text -∗ instr (mword_of_int (UC + 0x1e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (UC + 0x1e)%Z (mword_of_int 0x4481 : mword 16)
    (mword_of_int (UC + 0x1e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) ucdc_4481 exec_execute_C_LI. Qed.

  Lemma uci_20 : kernel_text -∗ instr (mword_of_int (UC + 0x20) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), LUI)).
  Proof. mk_rvc (UC + 0x20)%Z (mword_of_int 0x6a05 : mword 16)
    (mword_of_int (UC + 0x20) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), LUI)) ucdc_6a05 exec_execute_C_LUI. Qed.

  Lemma uci_22 : kernel_text -∗ instr (mword_of_int (UC + 0x22) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UC + 0x22)%Z (mword_of_int 0xa021 : mword 16)
    (mword_of_int (UC + 0x22) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)) cdec_a021 exec_execute_C_J. Qed.

  (* --- the loop back edge and its exit test ---------------------------- *)

  Lemma uci_24 : kernel_text -∗ instr (mword_of_int (UC + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UC + 0x24)%Z (mword_of_int 0x94d2 : mword 16)
    (mword_of_int (UC + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) ucdc_94d2 exec_execute_C_ADD. Qed.

  Lemma uci_26 : kernel_text -∗ instr (mword_of_int (UC + 0x26) : mword 64) false (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BGEU)).
  Proof. mk_base (UC + 0x26)%Z (mword_of_int 0x0554fc63 : mword 32)
    (mword_of_int (UC + 0x26) : mword 64) (BTYPE (mword_of_int 88 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 9), BGEU)) ucdb_0554fc63. Qed.

  (* --- loop head: walk(old, i, 0) -------------------------------------- *)

  Lemma uci_2a : kernel_text -∗ instr (mword_of_int (UC + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (UC + 0x2a)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (UC + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma uci_2c : kernel_text -∗ instr (mword_of_int (UC + 0x2c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (UC + 0x2c)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (UC + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma uci_2e : kernel_text -∗ instr (mword_of_int (UC + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UC + 0x2e)%Z (mword_of_int 0x855a : mword 16)
    (mword_of_int (UC + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 10), ADD)) cdec_855a exec_execute_C_MV. Qed.

  Lemma uci_30 : kernel_text -∗ instr (mword_of_int (UC + 0x30) : mword 64) false (JAL (mword_of_int 2095912 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x30)%Z (mword_of_int 0xb29ff0ef : mword 32)
    (mword_of_int (UC + 0x30) : mword 64) (JAL (mword_of_int 2095912 : mword 21, Regidx (mword_of_int 1))) ucdb_b29ff0ef. Qed.

  Lemma uci_34 : kernel_text -∗ instr (mword_of_int (UC + 0x34) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 248 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (UC + 0x34)%Z (mword_of_int 0xd965 : mword 16)
    (mword_of_int (UC + 0x34) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 248 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ucdc_d965 exec_execute_C_BEQZ. Qed.

  (* --- read the pte and test PTE_V ------------------------------------- *)

  Lemma uci_36 : kernel_text -∗ instr (mword_of_int (UC + 0x36) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), false, 8)).
  Proof. mk_base (UC + 0x36)%Z (mword_of_int 0x00053983 : mword 32)
    (mword_of_int (UC + 0x36) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 19), false, 8)) ucdb_00053983. Qed.

  Lemma uci_3a : kernel_text -∗ instr (mword_of_int (UC + 0x3a) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (UC + 0x3a)%Z (mword_of_int 0x0019f793 : mword 32)
    (mword_of_int (UC + 0x3a) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 15), ANDI)) ucdb_0019f793. Qed.

  Lemma uci_3e : kernel_text -∗ instr (mword_of_int (UC + 0x3e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (UC + 0x3e)%Z (mword_of_int 0xd3fd : mword 16)
    (mword_of_int (UC + 0x3e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) ucdc_d3fd exec_execute_C_BEQZ. Qed.

  (* --- kalloc / memmove the page --------------------------------------- *)

  Lemma uci_40 : kernel_text -∗ instr (mword_of_int (UC + 0x40) : mword 64) false (JAL (mword_of_int 2094826 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x40)%Z (mword_of_int 0xeeaff0ef : mword 32)
    (mword_of_int (UC + 0x40) : mword 64) (JAL (mword_of_int 2094826 : mword 21, Regidx (mword_of_int 1))) ucdb_eeaff0ef. Qed.

  Lemma uci_44 : kernel_text -∗ instr (mword_of_int (UC + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (UC + 0x44)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (UC + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma uci_46 : kernel_text -∗ instr (mword_of_int (UC + 0x46) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (UC + 0x46)%Z (mword_of_int 0xc11d : mword 16)
    (mword_of_int (UC + 0x46) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ucdc_c11d exec_execute_C_BEQZ. Qed.

  Lemma uci_48 : kernel_text -∗ instr (mword_of_int (UC + 0x48) : mword 64) false (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 11), SRLI)).
  Proof. mk_base (UC + 0x48)%Z (mword_of_int 0x00a9d593 : mword 32)
    (mword_of_int (UC + 0x48) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, Regidx (mword_of_int 19), Regidx (mword_of_int 11), SRLI)) ucdb_00a9d593. Qed.

  Lemma uci_4c : kernel_text -∗ instr (mword_of_int (UC + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (UC + 0x4c)%Z (mword_of_int 0x8652 : mword 16)
    (mword_of_int (UC + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)) ucdc_8652 exec_execute_C_MV. Qed.

  Lemma uci_4e : kernel_text -∗ instr (mword_of_int (UC + 0x4e) : mword 64) true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).
  Proof. mk_rvc (UC + 0x4e)%Z (mword_of_int 0x05b2 : mword 16)
    (mword_of_int (UC + 0x4e) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) ucdc_05b2 exec_execute_C_SLLI. Qed.

  Lemma uci_50 : kernel_text -∗ instr (mword_of_int (UC + 0x50) : mword 64) false (JAL (mword_of_int 2095316 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x50)%Z (mword_of_int 0x8d5ff0ef : mword 32)
    (mword_of_int (UC + 0x50) : mword 64) (JAL (mword_of_int 2095316 : mword 21, Regidx (mword_of_int 1))) ucdb_8d5ff0ef. Qed.

  (* --- mappages(new, i, PGSIZE, mem, flags) ---------------------------- *)

  Lemma uci_54 : kernel_text -∗ instr (mword_of_int (UC + 0x54) : mword 64) false (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_base (UC + 0x54)%Z (mword_of_int 0x3ff9f713 : mword 32)
    (mword_of_int (UC + 0x54) : mword 64) (ITYPE (mword_of_int 1023 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ANDI)) ucdb_3ff9f713. Qed.

  Lemma uci_58 : kernel_text -∗ instr (mword_of_int (UC + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (UC + 0x58)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (UC + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) ucdc_86ca exec_execute_C_MV. Qed.

  Lemma uci_5a : kernel_text -∗ instr (mword_of_int (UC + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (UC + 0x5a)%Z (mword_of_int 0x8652 : mword 16)
    (mword_of_int (UC + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 12), ADD)) ucdc_8652 exec_execute_C_MV. Qed.

  Lemma uci_5c : kernel_text -∗ instr (mword_of_int (UC + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (UC + 0x5c)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (UC + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma uci_5e : kernel_text -∗ instr (mword_of_int (UC + 0x5e) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UC + 0x5e)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (UC + 0x5e) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma uci_60 : kernel_text -∗ instr (mword_of_int (UC + 0x60) : mword 64) false (JAL (mword_of_int 2096076 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x60)%Z (mword_of_int 0xbcdff0ef : mword 32)
    (mword_of_int (UC + 0x60) : mword 64) (JAL (mword_of_int 2096076 : mword 21, Regidx (mword_of_int 1))) ucdb_bcdff0ef. Qed.

  Lemma uci_64 : kernel_text -∗ instr (mword_of_int (UC + 0x64) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 224 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (UC + 0x64)%Z (mword_of_int 0xd161 : mword 16)
    (mword_of_int (UC + 0x64) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 224 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) ucdc_d161 exec_execute_C_BEQZ. Qed.

  (* --- mappages failed: kfree the fresh page, then unwind -------------- *)

  Lemma uci_66 : kernel_text -∗ instr (mword_of_int (UC + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UC + 0x66)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (UC + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma uci_68 : kernel_text -∗ instr (mword_of_int (UC + 0x68) : mword 64) false (JAL (mword_of_int 2094554 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x68)%Z (mword_of_int 0xddaff0ef : mword 32)
    (mword_of_int (UC + 0x68) : mword 64) (JAL (mword_of_int 2094554 : mword 21, Regidx (mword_of_int 1))) ucdb_ddaff0ef. Qed.

  (* --- the error exit: uvmunmap(new, 0, i/PGSIZE, 1); return -1 -------- *)

  Lemma uci_6c : kernel_text -∗ instr (mword_of_int (UC + 0x6c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (UC + 0x6c)%Z (mword_of_int 0x4685 : mword 16)
    (mword_of_int (UC + 0x6c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) ucdc_4685 exec_execute_C_LI. Qed.

  Lemma uci_6e : kernel_text -∗ instr (mword_of_int (UC + 0x6e) : mword 64) false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 12), SRLI)).
  Proof. mk_base (UC + 0x6e)%Z (mword_of_int 0x00c4d613 : mword 32)
    (mword_of_int (UC + 0x6e) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 9), Regidx (mword_of_int 12), SRLI)) ucdb_00c4d613. Qed.

  Lemma uci_72 : kernel_text -∗ instr (mword_of_int (UC + 0x72) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (UC + 0x72)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (UC + 0x72) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma uci_74 : kernel_text -∗ instr (mword_of_int (UC + 0x74) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UC + 0x74)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (UC + 0x74) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma uci_76 : kernel_text -∗ instr (mword_of_int (UC + 0x76) : mword 64) false (JAL (mword_of_int 2096516 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x76)%Z (mword_of_int 0xd85ff0ef : mword 32)
    (mword_of_int (UC + 0x76) : mword 64) (JAL (mword_of_int 2096516 : mword 21, Regidx (mword_of_int 1))) ucdb_d85ff0ef. Qed.

  Lemma uci_7a : kernel_text -∗ instr (mword_of_int (UC + 0x7a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (UC + 0x7a)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (UC + 0x7a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma uci_7c : kernel_text -∗ instr (mword_of_int (UC + 0x7c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UC + 0x7c)%Z (mword_of_int 0xa011 : mword 16)
    (mword_of_int (UC + 0x7c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)) ucdc_a011 exec_execute_C_J. Qed.

  (* --- success: return 0 ----------------------------------------------- *)

  Lemma uci_7e : kernel_text -∗ instr (mword_of_int (UC + 0x7e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (UC + 0x7e)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (UC + 0x7e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* --- the common epilogue, fed by both arms (0x7c and 0x7e) ----------- *)

  Lemma uci_80 : kernel_text -∗ instr (mword_of_int (UC + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UC + 0x80)%Z (mword_of_int 0x60a6 : mword 16)
    (mword_of_int (UC + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.

  Lemma uci_82 : kernel_text -∗ instr (mword_of_int (UC + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UC + 0x82)%Z (mword_of_int 0x6406 : mword 16)
    (mword_of_int (UC + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.

  Lemma uci_84 : kernel_text -∗ instr (mword_of_int (UC + 0x84) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UC + 0x84)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (UC + 0x84) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma uci_86 : kernel_text -∗ instr (mword_of_int (UC + 0x86) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (UC + 0x86)%Z (mword_of_int 0x7942 : mword 16)
    (mword_of_int (UC + 0x86) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.

  Lemma uci_88 : kernel_text -∗ instr (mword_of_int (UC + 0x88) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (UC + 0x88)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (UC + 0x88) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma uci_8a : kernel_text -∗ instr (mword_of_int (UC + 0x8a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (UC + 0x8a)%Z (mword_of_int 0x7a02 : mword 16)
    (mword_of_int (UC + 0x8a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.

  Lemma uci_8c : kernel_text -∗ instr (mword_of_int (UC + 0x8c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (UC + 0x8c)%Z (mword_of_int 0x6ae2 : mword 16)
    (mword_of_int (UC + 0x8c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.

  Lemma uci_8e : kernel_text -∗ instr (mword_of_int (UC + 0x8e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (UC + 0x8e)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (UC + 0x8e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  Lemma uci_90 : kernel_text -∗ instr (mword_of_int (UC + 0x90) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (UC + 0x90)%Z (mword_of_int 0x6ba2 : mword 16)
    (mword_of_int (UC + 0x90) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.

  Lemma uci_92 : kernel_text -∗ instr (mword_of_int (UC + 0x92) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UC + 0x92)%Z (mword_of_int 0x6161 : mword 16)
    (mword_of_int (UC + 0x92) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.

  Lemma uci_94 : kernel_text -∗ instr (mword_of_int (UC + 0x94) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UC + 0x94)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UC + 0x94) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- sz == 0: return 0 with NO frame ever pushed --------------------- *)

  Lemma uci_96 : kernel_text -∗ instr (mword_of_int (UC + 0x96) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (UC + 0x96)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (UC + 0x96) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma uci_98 : kernel_text -∗ instr (mword_of_int (UC + 0x98) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UC + 0x98)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UC + 0x98) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End UvmcopyInstrs.

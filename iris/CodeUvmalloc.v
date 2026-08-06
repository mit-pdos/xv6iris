(* CodeUvmalloc.v -- the instruction-DECODE layer for xv6's uvmalloc().

     uvmalloc @ 0x800012cc .. 0x80001375   (offsets 0x00 .. 0xa8, 73 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([uai_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the eleven 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; uvmalloc's own words are local, named [uadc_<word>]
   (compressed) / [uadb_<word>] (base).

     uint64 uvmalloc(pagetable_t pagetable /*a0*/, uint64 oldsz /*a1*/,
                     uint64 newsz /*a2*/, int xperm /*a3*/)

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- the .asm listing has drifted by 0xe bytes):

     0x00 0ab66163    bltu  a2,a1,+0xa2          # -> 0xa2, newsz < oldsz
     0x04 715d        c.addi16sp sp,-80          # 80-byte frame (10 slots)
     0x06 e486        c.sdsp ra,72(sp)
     0x08 e0a2        c.sdsp s0,64(sp)
     0x0a f84a        c.sdsp s2,48(sp)
     0x0c f052        c.sdsp s4,32(sp)
     0x0e ec56        c.sdsp s5,24(sp)
     0x10 e45e        c.sdsp s7,8(sp)
     0x12 0880        c.addi4spn s0,sp,80
     0x14 8aaa        c.mv   s5,a0               # s5 := pagetable
     0x16 8a32        c.mv   s4,a2               # s4 := newsz
     0x18 6785        c.lui  a5,0x1
     0x1a 17fd        c.addi a5,a5,-1            # a5 := 0xfff
     0x1c 95be        c.add  a1,a1,a5
     0x1e 77fd        c.lui  a5,0xfffff          # a5 := -4096
     0x20 00f5f933    and   s2,a1,a5             # s2 := a := PGROUNDUP(oldsz)
     0x24 8bca        c.mv   s7,s2               # kept for uvmdealloc
     0x26 08c97063    bgeu  s2,a2,+0x80          # -> 0xa6, nothing to do
     0x2a fc26        c.sdsp s1,56(sp)           # s1/s3/s6: only if loop runs
     0x2c f44e        c.sdsp s3,40(sp)
     0x2e e85a        c.sdsp s6,16(sp)
     0x30 6985        c.lui  s3,0x1              # s3 := 4096
     0x32 0126eb13    ori   s6,a3,18             # s6 := xperm|PTE_R|PTE_U
     0x36 82dff0ef    jal   ra,kalloc            # 0x80000b2e   <- loop head
     0x3a 84aa        c.mv   s1,a0               # s1 := mem
     0x3c c50d        c.beqz a0,+0x2a            # -> 0x66, out of memory
     0x3e 864e        c.mv   a2,s3
     0x40 4581        c.li   a1,0
     0x42 9bbff0ef    jal   ra,memset            # 0x80000cc8
     0x46 875a        c.mv   a4,s6               # perm
     0x48 86a6        c.mv   a3,s1               # pa
     0x4a 864e        c.mv   a2,s3               # PGSIZE
     0x4c 85ca        c.mv   a1,s2               # a
     0x4e 8556        c.mv   a0,s5               # pagetable
     0x50 d15ff0ef    jal   ra,mappages          # 0x80001030
     0x54 e915        c.bnez a0,+0x34            # -> 0x88, mappages failed
     0x56 994e        c.add  s2,s2,s3            # a += PGSIZE
     0x58 fd496fe3    bltu  s2,s4,-0x22          # -> 0x36, loop back edge
     0x5c 8552        c.mv   a0,s4               # --- success: return newsz
     0x5e 74e2        c.ldsp s1,56(sp)
     0x60 79a2        c.ldsp s3,40(sp)
     0x62 6b42        c.ldsp s6,16(sp)
     0x64 a811        c.j    +0x14               # -> 0x78
     0x66 865e        c.mv   a2,s7               # --- kalloc failed
     0x68 85ca        c.mv   a1,s2
     0x6a 8556        c.mv   a0,s5
     0x6c f51ff0ef    jal   ra,uvmdealloc        # 0x80001288
     0x70 4501        c.li   a0,0
     0x72 74e2        c.ldsp s1,56(sp)
     0x74 79a2        c.ldsp s3,40(sp)
     0x76 6b42        c.ldsp s6,16(sp)
     0x78 60a6        c.ldsp ra,72(sp)           # --- the common epilogue
     0x7a 6406        c.ldsp s0,64(sp)
     0x7c 7942        c.ldsp s2,48(sp)
     0x7e 7a02        c.ldsp s4,32(sp)
     0x80 6ae2        c.ldsp s5,24(sp)
     0x82 6ba2        c.ldsp s7,8(sp)
     0x84 6161        c.addi16sp sp,80
     0x86 8082        c.ret
     0x88 8526        c.mv   a0,s1               # --- mappages failed
     0x8a ef0ff0ef    jal   ra,kfree             # 0x80000a46
     0x8e 865e        c.mv   a2,s7
     0x90 85ca        c.mv   a1,s2
     0x92 8556        c.mv   a0,s5
     0x94 f29ff0ef    jal   ra,uvmdealloc        # 0x80001288
     0x98 4501        c.li   a0,0
     0x9a 74e2        c.ldsp s1,56(sp)
     0x9c 79a2        c.ldsp s3,40(sp)
     0x9e 6b42        c.ldsp s6,16(sp)
     0xa0 bfe1        c.j    -0x28               # -> 0x78
     0xa2 852e        c.mv   a0,a1               # --- newsz < oldsz (NO frame)
     0xa4 8082        c.ret
     0xa6 8532        c.mv   a0,a2               # --- nothing to do
     0xa8 bfc1        c.j    -0x30               # -> 0x78

   Two structural oddities worth flagging for the WP layer above:

     * the FIRST instruction is a 4-byte [bltu] taken BEFORE the frame is
       pushed, so the 0xa2..0xa4 arm returns with sp untouched and never
       reaches the common epilogue at 0x78;
     * s1/s3/s6 are shrink-wrapped -- pushed at 0x2a..0x2e only once the
       loop is known to run, and popped on each of the three loop-exit arms
       (0x5e..0x62, 0x72..0x76, 0x9a..0x9e) before the join at 0x78.  The
       "nothing to do" arm at 0xa6 jumps to 0x78 without touching them.

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.j]s are 2028 / 2024 (2^11 complements of -20 / -24 half-words),
   the backward [bltu] at 0x58 is 8158 (2^13 complement of -34 bytes) and the
   backward [jal]s are 2095148 / 2095546 / 2096404 / 2096976 / 2094832 /
   2096936 (2^21 complements of the byte offsets).  For BTYPE/JAL the AST arg
   is the BYTE offset residue; for C_J / C_BEQZ / C_BNEZ it is the offset/2
   residue, re-widened by the [concat_vec ... 'b"0"] in the [instr] fact.   *)
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
Require Import KernelRvcDecode KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for uvmalloc's own words.                      *)
(*                                                                        *)
(* Reused straight from KernelRvcDecode.v (no local copy needed):         *)
(*   0x04 c.addi16sp sp,-80      [cdec_715d]                              *)
(*   0x06 c.sdsp ra,72(sp)       [cdec_e486]                              *)
(*   0x08 c.sdsp s0,64(sp)       [cdec_e0a2]                              *)
(*   0x0a c.sdsp s2,48(sp)       [cdec_f84a]                              *)
(*   0x0c c.sdsp s4,32(sp)       [cdec_f052]                              *)
(*   0x0e c.sdsp s5,24(sp)       [cdec_ec56]                              *)
(*   0x10 c.sdsp s7,8(sp)        [cdec_e45e]                              *)
(*   0x12 c.addi4spn s0,sp,80    [cdec_0880]                              *)
(*   0x2a c.sdsp s1,56(sp)       [cdec_fc26]                              *)
(*   0x2c c.sdsp s3,40(sp)       [cdec_f44e]                              *)
(*   0x2e c.sdsp s6,16(sp)       [cdec_e85a]                              *)
(*   0x3a c.mv  s1,a0            [cdec_84aa]                              *)
(*   0x40 c.li  a1,0             [cdec_4581]                              *)
(*   0x4c c.mv  a1,s2            [cdec_85ca]                              *)
(*   0x5c c.mv  a0,s4            [cdec_8552]                              *)
(*   0x5e c.ldsp s1,56(sp)       [cdec_74e2]                              *)
(*   0x60 c.ldsp s3,40(sp)       [cdec_79a2]                              *)
(*   0x62 c.ldsp s6,16(sp)       [cdec_6b42]                              *)
(*   0x70 c.li  a0,0             [cdec_4501]                              *)
(*   0x78 c.ldsp ra,72(sp)       [cdec_60a6]                              *)
(*   0x7a c.ldsp s0,64(sp)       [cdec_6406]                              *)
(*   0x7c c.ldsp s2,48(sp)       [cdec_7942]                              *)
(*   0x7e c.ldsp s4,32(sp)       [cdec_7a02]                              *)
(*   0x80 c.ldsp s5,24(sp)       [cdec_6ae2]                              *)
(*   0x82 c.ldsp s7,8(sp)        [cdec_6ba2]                              *)
(*   0x84 c.addi16sp sp,80       [cdec_6161]                              *)
(*   0x86 c.ret                  [cdec_8082]                              *)
(*   0x88 c.mv  a0,s1            [cdec_8526]                              *)
(* ===================================================================== *)


(* 0x16  c.mv s4,a2 *)
(* [cdec_8a32] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x18  c.lui a5,0x1 *)
(* [cdec_6785] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1a  c.addi a5,-1  (imm6 = 63, the 6-bit residue of -1) *)
(* [cdec_17fd] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1c  c.add a1,a5 *)
(* [cdec_95be] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1e  c.lui a5,0xfffff  (imm6 = 63, the 6-bit residue of -1) *)
(* [cdec_77fd] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x24  c.mv s7,s2 *)
Lemma uadc_8bca s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8bca : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 23), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x30  c.lui s3,0x1 *)
Lemma uadc_6985 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6985 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x3c  c.beqz a0,+0x2a  (offset/2 = 21) *)

(* [cdec_864e] -- shared, see KernelRvcDecode.v *)

(* 0x46  c.mv a4,s6 *)
Lemma uadc_875a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x875a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 14), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x48  c.mv a3,s1 *)
Lemma uadc_86a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86a6 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4e / 0x6a / 0x92  c.mv a0,s5 *)
(* [cdec_8556] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x54  c.bnez a0,+0x34  (offset/2 = 26) *)
Lemma uadc_e915 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe915 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 26, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x56  c.add s2,s3   -- a += PGSIZE *)
Lemma uadc_994e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x994e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x66 / 0x8e  c.mv a2,s7 *)
Lemma uadc_865e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x865e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa0  c.j -0x28  (offset/2 = -20; 11-bit residue 2028) *)
(* [cdec_bfe1] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0xa2  c.mv a0,a1 *)
Lemma uadc_852e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x852e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa6  c.mv a0,a2 *)
Lemma uadc_8532 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8532 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa8  c.j -0x30  (offset/2 = -24; 11-bit residue 2024) *)
Lemma uadc_bfc1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfc1 : mword 16)) s
  = Some (C_J (mword_of_int 2024), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all eleven are uvmalloc's own.           *)
(* ===================================================================== *)
(* 0x00  bltu a2,a1,+0xa2  -- the [newsz < oldsz] early return, BEFORE any push *)
Lemma uadb_0ab66163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0ab66163 : mword 32)) s
  = Some (BTYPE (mword_of_int 162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x20  and s2,a1,a5  -- a := PGROUNDUP(oldsz) *)
Lemma uadb_00f5f933 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f5f933 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 18), AND), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  bgeu s2,a2,+0x80  -- nothing to do *)
Lemma uadb_08c97063 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x08c97063 : mword 32)) s
  = Some (BTYPE (mword_of_int 128 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 18), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  ori s6,a3,18  -- s6 := xperm | PTE_R | PTE_U *)
Lemma uadb_0126eb13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0126eb13 : mword 32)) s
  = Some (ITYPE (mword_of_int 18 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 22), ORI), s).
Proof. decode_bridge_ms. Qed.

(* 0x36  jal ra,kalloc      (0x80001302 -> 0x80000b2e is -2004) *)
Lemma uadb_82dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x82dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095148 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x42  jal ra,memset      (0x8000130e -> 0x80000cc8 is -1606) *)
Lemma uadb_9bbff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9bbff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095546 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x50  jal ra,mappages    (0x8000131c -> 0x80001030 is -748) *)
Lemma uadb_d15ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd15ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096404 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x58  bltu s2,s4,-0x22  -- the loop back edge to 0x36 (13-bit residue 8158) *)
Lemma uadb_fd496fe3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd496fe3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x6c  jal ra,uvmdealloc  (0x80001338 -> 0x80001288 is -176) *)
(* [bdec_f51ff0ef] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x8a  jal ra,kfree       (0x80001356 -> 0x80000a46 is -2320) *)
Lemma uadb_ef0ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xef0ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094832 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x94  jal ra,uvmdealloc  (0x80001360 -> 0x80001288 is -216) *)
Lemma uadb_f29ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf29ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096936 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmallocInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* --- the frameless early return test --------------------------------- *)

  Lemma uai_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x00) : mword 64) false (BTYPE (mword_of_int 162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BLTU)).
  Proof. mk_base (KernelSyms.uvmalloc + 0x00)%Z (mword_of_int 0x0ab66163 : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x00) : mword 64) (BTYPE (mword_of_int 162 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BLTU)) uadb_0ab66163. Qed.

  (* --- prologue: the 80-byte frame ------------------------------------- *)

  Lemma uai_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x04) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x04)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x04) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  Lemma uai_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x06)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  Lemma uai_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x08)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  Lemma uai_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x0a)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  Lemma uai_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x0c)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  Lemma uai_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x0e)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  Lemma uai_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x10)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  Lemma uai_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x12) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x12)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x12) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  (* --- PGROUNDUP(oldsz) and the [a >= newsz] test ---------------------- *)

  Lemma uai_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x14)%Z (mword_of_int 0x8aaa : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)) cdec_8aaa exec_execute_C_MV. Qed.

  Lemma uai_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x16)%Z (mword_of_int 0x8a32 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a32 exec_execute_C_MV. Qed.

  Lemma uai_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x18) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x18)%Z (mword_of_int 0x6785 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x18) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)) cdec_6785 exec_execute_C_LUI. Qed.

  Lemma uai_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x1a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x1a)%Z (mword_of_int 0x17fd : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cdec_17fd exec_execute_C_ADDI. Qed.

  Lemma uai_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x1c)%Z (mword_of_int 0x95be : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)) cdec_95be exec_execute_C_ADD. Qed.

  Lemma uai_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x1e) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x1e)%Z (mword_of_int 0x77fd : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x1e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), LUI)) cdec_77fd exec_execute_C_LUI. Qed.

  Lemma uai_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x20) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 18), AND)).
  Proof. mk_base (KernelSyms.uvmalloc + 0x20)%Z (mword_of_int 0x00f5f933 : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 18), AND)) uadb_00f5f933. Qed.

  Lemma uai_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 23), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x24)%Z (mword_of_int 0x8bca : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 23), ADD)) uadc_8bca exec_execute_C_MV. Qed.

  Lemma uai_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x26) : mword 64) false (BTYPE (mword_of_int 128 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 18), BGEU)).
  Proof. mk_base (KernelSyms.uvmalloc + 0x26)%Z (mword_of_int 0x08c97063 : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x26) : mword 64) (BTYPE (mword_of_int 128 : mword 13, Regidx (mword_of_int 12), Regidx (mword_of_int 18), BGEU)) uadb_08c97063. Qed.

  (* --- the loop is entered: save s1/s3/s6 and set up ------------------ *)

  Lemma uai_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x2a)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  Lemma uai_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x2c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x2c)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x2c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  Lemma uai_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x2e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x2e)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x2e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  Lemma uai_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x30) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), LUI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x30)%Z (mword_of_int 0x6985 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x30) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), LUI)) uadc_6985 exec_execute_C_LUI. Qed.

  Lemma uai_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x32) : mword 64) false (ITYPE (mword_of_int 18 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 22), ORI)).
  Proof. mk_base (KernelSyms.uvmalloc + 0x32)%Z (mword_of_int 0x0126eb13 : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x32) : mword 64) (ITYPE (mword_of_int 18 : mword 12, Regidx (mword_of_int 13), Regidx (mword_of_int 22), ORI)) uadb_0126eb13. Qed.

  (* --- the loop body: kalloc / memset / mappages ---------------------- *)

  Lemma uai_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64) false (JAL (mword_of_int 2095148 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x36)%Z (mword_of_int 0x82dff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x36) : mword 64) (JAL (mword_of_int 2095148 : mword 21, Regidx (mword_of_int 1))) uadb_82dff0ef. Qed.

  Lemma uai_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x3a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma uai_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x3c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x3c)%Z (mword_of_int 0xc50d : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x3c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 21 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c50d exec_execute_C_BEQZ. Qed.

  Lemma uai_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x3e) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x3e)%Z (mword_of_int 0x864e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x3e) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)) cdec_864e exec_execute_C_MV. Qed.

  Lemma uai_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x40)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma uai_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x42) : mword 64) false (JAL (mword_of_int 2095546 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x42)%Z (mword_of_int 0x9bbff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x42) : mword 64) (JAL (mword_of_int 2095546 : mword 21, Regidx (mword_of_int 1))) uadb_9bbff0ef. Qed.

  Lemma uai_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x46)%Z (mword_of_int 0x875a : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 14), ADD)) uadc_875a exec_execute_C_MV. Qed.

  Lemma uai_48 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x48) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x48)%Z (mword_of_int 0x86a6 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x48) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 13), ADD)) uadc_86a6 exec_execute_C_MV. Qed.

  Lemma uai_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x4a) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x4a)%Z (mword_of_int 0x864e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 12), ADD)) cdec_864e exec_execute_C_MV. Qed.

  Lemma uai_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x4c)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma uai_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x4e) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x4e)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x4e) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  Lemma uai_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x50) : mword 64) false (JAL (mword_of_int 2096404 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x50)%Z (mword_of_int 0xd15ff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x50) : mword 64) (JAL (mword_of_int 2096404 : mword 21, Regidx (mword_of_int 1))) uadb_d15ff0ef. Qed.

  Lemma uai_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x54) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x54)%Z (mword_of_int 0xe915 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x54) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 26 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) uadc_e915 exec_execute_C_BNEZ. Qed.

  Lemma uai_56 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x56) : mword 64) true (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x56)%Z (mword_of_int 0x994e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) uadc_994e exec_execute_C_ADD. Qed.

  Lemma uai_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x58) : mword 64) false (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BLTU)).
  Proof. mk_base (KernelSyms.uvmalloc + 0x58)%Z (mword_of_int 0xfd496fe3 : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x58) : mword 64) (BTYPE (mword_of_int 8158 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 18), BLTU)) uadb_fd496fe3. Qed.

  (* --- loop finished: return newsz ------------------------------------ *)

  Lemma uai_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x5c)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  Lemma uai_5e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x5e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x5e)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x5e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma uai_60 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x60) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x60)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x60) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma uai_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x62) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x62)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x62) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  Lemma uai_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x64) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x64)%Z (mword_of_int 0xa811 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x64) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")), zreg)) cdec_a811 exec_execute_C_J. Qed.

  (* --- kalloc returned 0: uvmdealloc back and return 0 ---------------- *)

  Lemma uai_66 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x66)%Z (mword_of_int 0x865e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)) uadc_865e exec_execute_C_MV. Qed.

  Lemma uai_68 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x68) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x68)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x68) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma uai_6a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x6a) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x6a)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x6a) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  Lemma uai_6c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x6c) : mword 64) false (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x6c)%Z (mword_of_int 0xf51ff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x6c) : mword 64) (JAL (mword_of_int 2096976 : mword 21, Regidx (mword_of_int 1))) bdec_f51ff0ef. Qed.

  Lemma uai_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x70) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x70)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x70) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma uai_72 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x72) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x72)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x72) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma uai_74 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x74) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x74)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x74) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma uai_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x76)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  (* --- the common epilogue, fed by four arms (0x64, 0x76, 0xa0, 0xa8) -- *)

  Lemma uai_78 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x78)%Z (mword_of_int 0x60a6 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.

  Lemma uai_7a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x7a)%Z (mword_of_int 0x6406 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.

  Lemma uai_7c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x7c)%Z (mword_of_int 0x7942 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.

  Lemma uai_7e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x7e)%Z (mword_of_int 0x7a02 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.

  Lemma uai_80 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x80)%Z (mword_of_int 0x6ae2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.

  Lemma uai_82 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x82)%Z (mword_of_int 0x6ba2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.

  Lemma uai_84 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x84) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x84)%Z (mword_of_int 0x6161 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x84) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.

  Lemma uai_86 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x86) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x86)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x86) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- mappages failed: kfree, uvmdealloc, return 0 ------------------- *)

  Lemma uai_88 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x88) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x88)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x88) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma uai_8a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x8a) : mword 64) false (JAL (mword_of_int 2094832 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x8a)%Z (mword_of_int 0xef0ff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x8a) : mword 64) (JAL (mword_of_int 2094832 : mword 21, Regidx (mword_of_int 1))) uadb_ef0ff0ef. Qed.

  Lemma uai_8e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x8e) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x8e)%Z (mword_of_int 0x865e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x8e) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 12), ADD)) uadc_865e exec_execute_C_MV. Qed.

  Lemma uai_90 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x90) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x90)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x90) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma uai_92 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x92) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x92)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x92) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  Lemma uai_94 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x94) : mword 64) false (JAL (mword_of_int 2096936 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmalloc + 0x94)%Z (mword_of_int 0xf29ff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmalloc + 0x94) : mword 64) (JAL (mword_of_int 2096936 : mword 21, Regidx (mword_of_int 1))) uadb_f29ff0ef. Qed.

  Lemma uai_98 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x98) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x98)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x98) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma uai_9a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x9a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x9a)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x9a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma uai_9c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x9c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x9c)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x9c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma uai_9e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0x9e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0x9e)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0x9e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  Lemma uai_a0 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0xa0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0xa0)%Z (mword_of_int 0xbfe1 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0xa0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2028 : mword 11) ('b"0")), zreg)) cdec_bfe1 exec_execute_C_J. Qed.

  (* --- newsz < oldsz: return oldsz; NO frame was ever pushed ---------- *)

  Lemma uai_a2 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0xa2) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0xa2)%Z (mword_of_int 0x852e : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0xa2) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 10), ADD)) uadc_852e exec_execute_C_MV. Qed.

  Lemma uai_a4 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0xa4) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0xa4)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0xa4) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- nothing to do (a >= newsz): return newsz ----------------------- *)

  Lemma uai_a6 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0xa6) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0xa6)%Z (mword_of_int 0x8532 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0xa6) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 10), ADD)) uadc_8532 exec_execute_C_MV. Qed.

  Lemma uai_a8 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmalloc + 0xa8) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.uvmalloc + 0xa8)%Z (mword_of_int 0xbfc1 : mword 16)
    (mword_of_int (KernelSyms.uvmalloc + 0xa8) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2024 : mword 11) ('b"0")), zreg)) uadc_bfc1 exec_execute_C_J. Qed.

End UvmallocInstrs.

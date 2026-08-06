(* CodeCopyout.v -- the instruction-DECODE layer for xv6's copyout().

     copyout @ 0x80001624 .. 0x800016e1   (offsets 0x00 .. 0xbc, 81 in all,
                                           KernelSyms.copyout, 0xbe bytes)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([coi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the fourteen 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>] -- the whole 96-byte-frame push/pop set (0x711d .. 0x1080 and
   0x60e6 .. 0x6125) shared verbatim with copyin, the argument/result moves
   0x8a2e / 0x8b32 / 0x8baa / 0x85da / 0x85a6 / 0x855e / 0x89aa and the
   [c.li a2,0] 0x4601, plus 0x611c / 0x4501 / 0x8082 / 0x557d / 0xbff9;
   copyout's own words are local, named [codc_<word>] (compressed) /
   [codb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which is stale by 14 bytes for this function; the C is
   kernel/vm.c's user-copy loop, walkaddr with a lazy-allocation fault-in and
   an explicit PTE_W check):

     0x00 cad1      beqz  a3,+0x94            # n == 0: nothing to copy
     0x02 711d      addi  sp,sp,-96           # 96-byte frame; ra/s0 + s1..s10 all saved
     0x04 ec86      sd    ra,88(sp)
     0x06 e8a2      sd    s0,80(sp)
     0x08 e4a6      sd    s1,72(sp)
     0x0a e0ca      sd    s2,64(sp)
     0x0c fc4e      sd    s3,56(sp)
     0x0e f852      sd    s4,48(sp)
     0x10 f456      sd    s5,40(sp)
     0x12 f05a      sd    s6,32(sp)
     0x14 ec5e      sd    s7,24(sp)
     0x16 e862      sd    s8,16(sp)
     0x18 e466      sd    s9,8(sp)
     0x1a e06a      sd    s10,0(sp)
     0x1c 1080      addi  s0,sp,96
     0x1e 8baa      mv    s7,a0               # s7 := pagetable
     0x20 8a2e      mv    s4,a1               # s4 := dstva (the running dst cursor)
     0x22 8b32      mv    s6,a2               # s6 := src
     0x24 8ab6      mv    s5,a3               # s5 := len (bytes left)
     0x26 7d7d      lui   s10,0xfffff         # s10 := -4096, the PGROUNDDOWN mask
     0x28 5cfd      li    s9,-1               # s9 := -1 ...
     0x2a 01acdc93  srli  s9,s9,0x1a          # ... >> 26 = MAXVA-1 = 0x3fffffffff
     0x2e 6c05      lui   s8,0x1              # s8 := PGSIZE
     0x30 a005      j     +0x50               # into the loop test
     0x32 409a0533  sub   a0,s4,s1            # a0 := dstva - va0
     0x36 0009061b  sext.w a2,s2              # a2 := (uint)n
     0x3a 85da      mv    a1,s6               # a1 := src
     0x3c 954e      add   a0,a0,s3            # a0 := pa0 + (dstva - va0)
     0x3e ec6ff0ef  jal   memmove             # memmove(pa0+off, src, n)
     0x42 412a8ab3  sub   s5,s5,s2            # len -= n
     0x46 9b4a      add   s6,s6,s2            # src += n
     0x48 01848a33  add   s4,s1,s8            # dstva = va0 + PGSIZE
     0x4c 040a8263  beqz  s5,+0x90            # len == 0 -> return 0
     0x50 01aa74b3  and   s1,s4,s10           # va0 := PGROUNDDOWN(dstva)  <- LOOP HEAD
     0x54 049ce263  bltu  s9,s1,+0x98         # va0 > MAXVA-1 -> return -1
     0x58 85a6      mv    a1,s1
     0x5a 855e      mv    a0,s7
     0x5c 977ff0ef  jal   walkaddr            # pa0 := walkaddr(pagetable, va0)
     0x60 89aa      mv    s3,a0               # s3 := pa0
     0x62 e901      bnez  a0,+0x72            # mapped -> skip the fault-in
     0x64 4601      li    a2,0
     0x66 85a6      mv    a1,s1
     0x68 855e      mv    a0,s7
     0x6a f13ff0ef  jal   vmfault             # pa0 := vmfault(pagetable, va0, 0)
     0x6e 89aa      mv    s3,a0               # s3 := pa0
     0x70 c139      beqz  a0,+0xb6            # vmfault failed -> return -1
     0x72 4601      li    a2,0
     0x74 85a6      mv    a1,s1
     0x76 855e      mv    a0,s7
     0x78 8c1ff0ef  jal   walk                # pte := walk(pagetable, va0, 0)
     0x7c 611c      ld    a5,0(a0)            # *pte
     0x7e 8b91      andi  a5,a5,4             # PTE_W
     0x80 cf8d      beqz  a5,+0xba            # not writable -> return -1
     0x82 41448933  sub   s2,s1,s4            # n := va0 - dstva ...
     0x86 9962      add   s2,s2,s8            # ... + PGSIZE
     0x88 fb2af5e3  bgeu  s5,s2,+0x32         # n <= len -> copy n
     0x8c 8956      mv    s2,s5               # else clamp n := len
     0x8e b755      j     +0x32               # -> +0x32
     0x90 4501      li    a0,0                # the len == 0 exit
     0x92 a021      j     +0x9a               # -> +0x9a, the pop
     0x94 4501      li    a0,0                # the n == 0 exit: no frame to pop
     0x96 8082      ret
     0x98 557d      li    a0,-1               # the va0 > MAXVA-1 exit
     0x9a 60e6      ld    ra,88(sp)           # <- THE COMMON EPILOGUE (four arms)
     0x9c 6446      ld    s0,80(sp)
     0x9e 64a6      ld    s1,72(sp)
     0xa0 6906      ld    s2,64(sp)
     0xa2 79e2      ld    s3,56(sp)
     0xa4 7a42      ld    s4,48(sp)
     0xa6 7aa2      ld    s5,40(sp)
     0xa8 7b02      ld    s6,32(sp)
     0xaa 6be2      ld    s7,24(sp)
     0xac 6c42      ld    s8,16(sp)
     0xae 6ca2      ld    s9,8(sp)
     0xb0 6d02      ld    s10,0(sp)
     0xb2 6125      addi  sp,sp,96
     0xb4 8082      ret
     0xb6 557d      li    a0,-1               # the vmfault-failed exit
     0xb8 b7cd      j     +0x9a               # -> +0x9a
     0xba 557d      li    a0,-1               # the not-writable exit
     0xbc bff9      j     +0x9a               # -> +0x9a

   The loop runs walkaddr / (vmfault) / walk once per destination page and
   memmoves the intra-page piece; FOUR exits reach the 96-byte pop at +0x9a
   (len exhausted, va0 out of range, vmfault failed, PTE_W clear), and a
   FIFTH -- the [n == 0] early-out at +0x94 -- returns from +0x96 without ever
   building a frame, because the guard at +0x00 precedes the prologue.

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.j]s are 2002 / 2033 / 2031 (2^11 complements of -46 / -15 / -17
   half-words), the backward [bgeu] is 8106 (2^13 - 86), and the four [jal]s
   are 2094790 / 2095478 / 2096914 / 2095296 (2^21 complements of -2362 to
   memmove, -1674 to walkaddr, -238 to vmfault, -1856 to walk).            *)
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
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for copyout's own words.                       *)
(* ===================================================================== *)

(* 0x00  beqz  a3,+0x94 *)
Lemma codc_cad1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcad1 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 74, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1a  sd    s10,0(sp) *)
Lemma codc_e06a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe06a : mword 16)) s
  = Some (C_SDSP (mword_of_int 0, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x24  mv    s5,a3 *)
(* [cdec_8ab6] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x26  lui   s10,0xfffff *)
Lemma codc_7d7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7d7d : mword 16)) s
  = Some (C_LUI (mword_of_int 63, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x28  li    s9,-1 *)
Lemma codc_5cfd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x5cfd : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2e  lui   s8,0x1 *)
Lemma codc_6c05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6c05 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x3c  add   a0,a0,s3 *)
Lemma codc_954e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x954e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 10), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x46  add   s6,s6,s2 *)
Lemma codc_9b4a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9b4a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 22), Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x62  bnez  a0,+0x72 *)
Lemma codc_e901 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe901 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 8, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x70  beqz  a0,+0xb6 *)
Lemma codc_c139 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc139 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 35, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x7e  andi  a5,a5,4 *)
Lemma codc_8b91 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8b91 : mword 16)) s
  = Some (C_ANDI (mword_of_int 4, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x80  beqz  a5,+0xba *)
Lemma codc_cf8d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf8d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 29, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x86  add   s2,s2,s8 *)
Lemma codc_9962 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9962 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8c  mv    s2,s5 *)
Lemma codc_8956 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8956 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8e  j     +0x32 *)
Lemma codc_b755 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb755 : mword 16)) s
  = Some (C_J (mword_of_int 2002 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb0  ld    s10,0(sp) *)
Lemma codc_6d02 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6d02 : mword 16)) s
  = Some (C_LDSP (mword_of_int 0, Regidx (mword_of_int 26)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_b7cd] -- shared, see KernelRvcDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all fourteen are copyout's own.          *)
(* ===================================================================== *)

(* 0x2a  srli  s9,s9,0x1a *)
Lemma codb_01acdc93 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01acdc93 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 26 : mword 6, Regidx (mword_of_int 25), Regidx (mword_of_int 25), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  sub   a0,s4,s1 *)
Lemma codb_409a0533 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x409a0533 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 10), SUB), s).
Proof. decode_bridge_ms. Qed.


(* 0x3e  jal   memmove *)
Lemma codb_ec6ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xec6ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094790 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x42  sub   s5,s5,s2 *)
Lemma codb_412a8ab3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x412a8ab3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 21), Regidx (mword_of_int 21), SUB), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  add   s4,s1,s8 *)
Lemma codb_01848a33 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01848a33 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 20), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x4c  beqz  s5,+0x90 *)
Lemma codb_040a8263 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x040a8263 : mword 32)) s
  = Some (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x50  and   s1,s4,s10 *)
Lemma codb_01aa74b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01aa74b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 26), Regidx (mword_of_int 20), Regidx (mword_of_int 9), AND), s).
Proof. decode_bridge_ms. Qed.

(* 0x54  bltu  s9,s1,+0x98 *)
Lemma codb_049ce263 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x049ce263 : mword 32)) s
  = Some (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 25), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x5c  jal   walkaddr *)
Lemma codb_977ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x977ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095478 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x6a  jal   vmfault *)
Lemma codb_f13ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf13ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096914 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x78  jal   walk *)
Lemma codb_8c1ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8c1ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095296 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x82  sub   s2,s1,s4 *)
Lemma codb_41448933 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x41448933 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 18), SUB), s).
Proof. decode_bridge_ms. Qed.

(* 0x88  bgeu  s5,s2,+0x32 *)
Lemma codb_fb2af5e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfb2af5e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8106 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 21), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(* The one leaf-form C_* -> base expansion copyout needs of its own       *)
(* (0x611c's is KernelRvcDecode's [cexec_611c]).                          *)
(* ===================================================================== *)

(* 0x7e  c.andi a5,4  -- the PTE_W test *)
Lemma coexec_8b91 s :
  exec (execute (C_ANDI (mword_of_int 4, Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section CopyoutInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Local Notation COP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.copyout + off) : mword 64) rvc ast).

  (* --- the n == 0 guard, then the 96-byte prologue --------------------- *)

  Lemma coi_00 : COP 0x00 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 74 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)).  (* beqz  a3,+0x94 -- n == 0: nothing to copy *)
  Proof. mk_rvc (KernelSyms.copyout + 0x00)%Z (mword_of_int 0xcad1 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x00) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 74 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)) codc_cad1 exec_execute_C_BEQZ. Qed.

  Lemma coi_02 : COP 0x02 true (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)).  (* addi  sp,sp,-96 -- 96-byte frame; ra/s0 + s1..s10 all saved *)
  Proof. mk_rvc (KernelSyms.copyout + 0x02)%Z (mword_of_int 0x711d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x02) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)) cdec_711d exec_execute_C_ADDI16SP. Qed.

  Lemma coi_04 : COP 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* sd    ra,88(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x04)%Z (mword_of_int 0xec86 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec86 exec_execute_C_SDSP. Qed.

  Lemma coi_06 : COP 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* sd    s0,80(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x06)%Z (mword_of_int 0xe8a2 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e8a2 exec_execute_C_SDSP. Qed.

  Lemma coi_08 : COP 0x08 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* sd    s1,72(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x08)%Z (mword_of_int 0xe4a6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e4a6 exec_execute_C_SDSP. Qed.

  Lemma coi_0a : COP 0x0a true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* sd    s2,64(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x0a)%Z (mword_of_int 0xe0ca : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e0ca exec_execute_C_SDSP. Qed.

  Lemma coi_0c : COP 0x0c true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).  (* sd    s3,56(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x0c)%Z (mword_of_int 0xfc4e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_fc4e exec_execute_C_SDSP. Qed.

  Lemma coi_0e : COP 0x0e true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).  (* sd    s4,48(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x0e)%Z (mword_of_int 0xf852 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f852 exec_execute_C_SDSP. Qed.

  Lemma coi_10 : COP 0x10 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).  (* sd    s5,40(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x10)%Z (mword_of_int 0xf456 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_f456 exec_execute_C_SDSP. Qed.

  Lemma coi_12 : COP 0x12 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).  (* sd    s6,32(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x12)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  Lemma coi_14 : COP 0x14 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).  (* sd    s7,24(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x14)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  Lemma coi_16 : COP 0x16 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).  (* sd    s8,16(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x16)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x16) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  Lemma coi_18 : COP 0x18 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)).  (* sd    s9,8(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x18)%Z (mword_of_int 0xe466 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x18) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)) cdec_e466 exec_execute_C_SDSP. Qed.

  Lemma coi_1a : COP 0x1a true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)).  (* sd    s10,0(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x1a)%Z (mword_of_int 0xe06a : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x1a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 26), sp, 8)) codc_e06a exec_execute_C_SDSP. Qed.

  Lemma coi_1c : COP 0x1c true (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* addi  s0,sp,96 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x1c)%Z (mword_of_int 0x1080 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x1c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1080 exec_execute_C_ADDI4SPN. Qed.

  (* --- argument shuffle and the loop constants ------------------------- *)

  Lemma coi_1e : COP 0x1e true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 23), ADD)).  (* mv    s7,a0 -- s7 := pagetable *)
  Proof. mk_rvc (KernelSyms.copyout + 0x1e)%Z (mword_of_int 0x8baa : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 23), ADD)) cdec_8baa exec_execute_C_MV. Qed.

  Lemma coi_20 : COP 0x20 true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)).  (* mv    s4,a1 -- s4 := dstva (the running dst cursor) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x20)%Z (mword_of_int 0x8a2e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2e exec_execute_C_MV. Qed.

  Lemma coi_22 : COP 0x22 true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 22), ADD)).  (* mv    s6,a2 -- s6 := src *)
  Proof. mk_rvc (KernelSyms.copyout + 0x22)%Z (mword_of_int 0x8b32 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 22), ADD)) cdec_8b32 exec_execute_C_MV. Qed.

  Lemma coi_24 : COP 0x24 true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 21), ADD)).  (* mv    s5,a3 -- s5 := len (bytes left) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x24)%Z (mword_of_int 0x8ab6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 21), ADD)) cdec_8ab6 exec_execute_C_MV. Qed.

  Lemma coi_26 : COP 0x26 true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 26), LUI)).  (* lui   s10,0xfffff -- s10 := -4096, the PGROUNDDOWN mask *)
  Proof. mk_rvc (KernelSyms.copyout + 0x26)%Z (mword_of_int 0x7d7d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x26) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 26), LUI)) codc_7d7d exec_execute_C_LUI. Qed.

  Lemma coi_28 : COP 0x28 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 25), ADDI)).  (* li    s9,-1 -- s9 := -1 ... *)
  Proof. mk_rvc (KernelSyms.copyout + 0x28)%Z (mword_of_int 0x5cfd : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 25), ADDI)) codc_5cfd exec_execute_C_LI. Qed.

  Lemma coi_2a : COP 0x2a false (SHIFTIOP (mword_of_int 26 : mword 6, Regidx (mword_of_int 25), Regidx (mword_of_int 25), SRLI)).  (* srli  s9,s9,0x1a -- ... >> 26 = MAXVA-1 = 0x3fffffffff *)
  Proof. mk_base (KernelSyms.copyout + 0x2a)%Z (mword_of_int 0x01acdc93 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x2a) : mword 64) (SHIFTIOP (mword_of_int 26 : mword 6, Regidx (mword_of_int 25), Regidx (mword_of_int 25), SRLI)) codb_01acdc93. Qed.

  Lemma coi_2e : COP 0x2e true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 24), LUI)).  (* lui   s8,0x1 -- s8 := PGSIZE *)
  Proof. mk_rvc (KernelSyms.copyout + 0x2e)%Z (mword_of_int 0x6c05 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x2e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 24), LUI)) codc_6c05 exec_execute_C_LUI. Qed.

  Lemma coi_30 : COP 0x30 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")), zreg)).  (* j     +0x50 -- into the loop test *)
  Proof. mk_rvc (KernelSyms.copyout + 0x30)%Z (mword_of_int 0xa005 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x30) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 16 : mword 11) ('b"0")), zreg)) cdec_a005 exec_execute_C_J. Qed.

  (* --- the memmove body and the cursor bumps (loop tail) --------------- *)

  Lemma coi_32 : COP 0x32 false (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 10), SUB)).  (* sub   a0,s4,s1 -- a0 := dstva - va0 *)
  Proof. mk_base (KernelSyms.copyout + 0x32)%Z (mword_of_int 0x409a0533 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 10), SUB)) codb_409a0533. Qed.

  Lemma coi_36 : COP 0x36 false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))).  (* sext.w a2,s2 -- a2 := (uint)n *)
  Proof. mk_base (KernelSyms.copyout + 0x36)%Z (mword_of_int 0x0009061b : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x36) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 12))) bdec_0009061b. Qed.

  Lemma coi_3a : COP 0x3a true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)).  (* mv    a1,s6 -- a1 := src *)
  Proof. mk_rvc (KernelSyms.copyout + 0x3a)%Z (mword_of_int 0x85da : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 11), ADD)) cdec_85da exec_execute_C_MV. Qed.

  Lemma coi_3c : COP 0x3c true (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).  (* add   a0,a0,s3 -- a0 := pa0 + (dstva - va0) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x3c)%Z (mword_of_int 0x954e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) codc_954e exec_execute_C_ADD. Qed.

  Lemma coi_3e : COP 0x3e false (JAL (mword_of_int 2094790 : mword 21, Regidx (mword_of_int 1))).  (* jal   memmove -- memmove(pa0+off, src, n) *)
  Proof. mk_base (KernelSyms.copyout + 0x3e)%Z (mword_of_int 0xec6ff0ef : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x3e) : mword 64) (JAL (mword_of_int 2094790 : mword 21, Regidx (mword_of_int 1))) codb_ec6ff0ef. Qed.

  Lemma coi_42 : COP 0x42 false (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 21), Regidx (mword_of_int 21), SUB)).  (* sub   s5,s5,s2 -- len -= n *)
  Proof. mk_base (KernelSyms.copyout + 0x42)%Z (mword_of_int 0x412a8ab3 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 21), Regidx (mword_of_int 21), SUB)) codb_412a8ab3. Qed.

  Lemma coi_46 : COP 0x46 true (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADD)).  (* add   s6,s6,s2 -- src += n *)
  Proof. mk_rvc (KernelSyms.copyout + 0x46)%Z (mword_of_int 0x9b4a : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADD)) codc_9b4a exec_execute_C_ADD. Qed.

  Lemma coi_48 : COP 0x48 false (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 20), ADD)).  (* add   s4,s1,s8 -- dstva = va0 + PGSIZE *)
  Proof. mk_base (KernelSyms.copyout + 0x48)%Z (mword_of_int 0x01848a33 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x48) : mword 64) (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 9), Regidx (mword_of_int 20), ADD)) codb_01848a33. Qed.

  Lemma coi_4c : COP 0x4c false (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)).  (* beqz  s5,+0x90 -- len == 0 -> return 0 *)
  Proof. mk_base (KernelSyms.copyout + 0x4c)%Z (mword_of_int 0x040a8263 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x4c) : mword 64) (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BEQ)) codb_040a8263. Qed.

  (* --- LOOP HEAD: PGROUNDDOWN, range check, walkaddr ------------------- *)

  Lemma coi_50 : COP 0x50 false (RTYPE (Regidx (mword_of_int 26), Regidx (mword_of_int 20), Regidx (mword_of_int 9), AND)).  (* and   s1,s4,s10 -- va0 := PGROUNDDOWN(dstva)  <- LOOP HEAD *)
  Proof. mk_base (KernelSyms.copyout + 0x50)%Z (mword_of_int 0x01aa74b3 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 26), Regidx (mword_of_int 20), Regidx (mword_of_int 9), AND)) codb_01aa74b3. Qed.

  Lemma coi_54 : COP 0x54 false (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 25), BLTU)).  (* bltu  s9,s1,+0x98 -- va0 > MAXVA-1 -> return -1 *)
  Proof. mk_base (KernelSyms.copyout + 0x54)%Z (mword_of_int 0x049ce263 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x54) : mword 64) (BTYPE (mword_of_int 68 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 25), BLTU)) codb_049ce263. Qed.

  Lemma coi_58 : COP 0x58 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).  (* mv    a1,s1 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x58)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma coi_5a : COP 0x5a true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).  (* mv    a0,s7 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x5a)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma coi_5c : COP 0x5c false (JAL (mword_of_int 2095478 : mword 21, Regidx (mword_of_int 1))).  (* jal   walkaddr -- pa0 := walkaddr(pagetable, va0) *)
  Proof. mk_base (KernelSyms.copyout + 0x5c)%Z (mword_of_int 0x977ff0ef : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x5c) : mword 64) (JAL (mword_of_int 2095478 : mword 21, Regidx (mword_of_int 1))) codb_977ff0ef. Qed.

  Lemma coi_60 : COP 0x60 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).  (* mv    s3,a0 -- s3 := pa0 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x60)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x60) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma coi_62 : COP 0x62 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).  (* bnez  a0,+0x72 -- mapped -> skip the fault-in *)
  Proof. mk_rvc (KernelSyms.copyout + 0x62)%Z (mword_of_int 0xe901 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x62) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) codc_e901 exec_execute_C_BNEZ. Qed.

  (* --- walkaddr missed: fault the page in ------------------------------ *)

  Lemma coi_64 : COP 0x64 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).  (* li    a2,0 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x64)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x64) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma coi_66 : COP 0x66 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).  (* mv    a1,s1 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x66)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma coi_68 : COP 0x68 true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).  (* mv    a0,s7 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x68)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x68) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma coi_6a : COP 0x6a false (JAL (mword_of_int 2096914 : mword 21, Regidx (mword_of_int 1))).  (* jal   vmfault -- pa0 := vmfault(pagetable, va0, 0) *)
  Proof. mk_base (KernelSyms.copyout + 0x6a)%Z (mword_of_int 0xf13ff0ef : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x6a) : mword 64) (JAL (mword_of_int 2096914 : mword 21, Regidx (mword_of_int 1))) codb_f13ff0ef. Qed.

  Lemma coi_6e : COP 0x6e true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).  (* mv    s3,a0 -- s3 := pa0 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x6e)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x6e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma coi_70 : COP 0x70 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 35 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).  (* beqz  a0,+0xb6 -- vmfault failed -> return -1 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x70)%Z (mword_of_int 0xc139 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x70) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 35 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) codc_c139 exec_execute_C_BEQZ. Qed.

  (* --- re-walk for the PTE and check PTE_W ----------------------------- *)

  Lemma coi_72 : COP 0x72 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).  (* li    a2,0 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x72)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x72) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma coi_74 : COP 0x74 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).  (* mv    a1,s1 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x74)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x74) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  Lemma coi_76 : COP 0x76 true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).  (* mv    a0,s7 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x76)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x76) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma coi_78 : COP 0x78 false (JAL (mword_of_int 2095296 : mword 21, Regidx (mword_of_int 1))).  (* jal   walk -- pte := walk(pagetable, va0, 0) *)
  Proof. mk_base (KernelSyms.copyout + 0x78)%Z (mword_of_int 0x8c1ff0ef : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x78) : mword 64) (JAL (mword_of_int 2095296 : mword 21, Regidx (mword_of_int 1))) codb_8c1ff0ef. Qed.

  Lemma coi_7c : COP 0x7c true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).  (* ld    a5,0(a0) -- *pte *)
  Proof. mk_rvc (KernelSyms.copyout + 0x7c)%Z (mword_of_int 0x611c : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x7c) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) cdec_611c cexec_611c. Qed.

  Lemma coi_7e : COP 0x7e true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).  (* andi  a5,a5,4 -- PTE_W *)
  Proof. mk_rvc (KernelSyms.copyout + 0x7e)%Z (mword_of_int 0x8b91 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x7e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) codc_8b91 coexec_8b91. Qed.

  Lemma coi_80 : COP 0x80 true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).  (* beqz  a5,+0xba -- not writable -> return -1 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x80)%Z (mword_of_int 0xcf8d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x80) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) codc_cf8d exec_execute_C_BEQZ. Qed.

  (* --- n = min(PGSIZE - (dstva - va0), len) ---------------------------- *)

  Lemma coi_82 : COP 0x82 false (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 18), SUB)).  (* sub   s2,s1,s4 -- n := va0 - dstva ... *)
  Proof. mk_base (KernelSyms.copyout + 0x82)%Z (mword_of_int 0x41448933 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x82) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 9), Regidx (mword_of_int 18), SUB)) codb_41448933. Qed.

  Lemma coi_86 : COP 0x86 true (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).  (* add   s2,s2,s8 -- ... + PGSIZE *)
  Proof. mk_rvc (KernelSyms.copyout + 0x86)%Z (mword_of_int 0x9962 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x86) : mword 64) (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) codc_9962 exec_execute_C_ADD. Qed.

  Lemma coi_88 : COP 0x88 false (BTYPE (mword_of_int 8106 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 21), BGEU)).  (* bgeu  s5,s2,+0x32 -- n <= len -> copy n *)
  Proof. mk_base (KernelSyms.copyout + 0x88)%Z (mword_of_int 0xfb2af5e3 : mword 32)
    (mword_of_int (KernelSyms.copyout + 0x88) : mword 64) (BTYPE (mword_of_int 8106 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 21), BGEU)) codb_fb2af5e3. Qed.

  Lemma coi_8c : COP 0x8c true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 18), ADD)).  (* mv    s2,s5 -- else clamp n := len *)
  Proof. mk_rvc (KernelSyms.copyout + 0x8c)%Z (mword_of_int 0x8956 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x8c) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 18), ADD)) codc_8956 exec_execute_C_MV. Qed.

  Lemma coi_8e : COP 0x8e true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")), zreg)).  (* j     +0x32 -- -> +0x32 *)
  Proof. mk_rvc (KernelSyms.copyout + 0x8e)%Z (mword_of_int 0xb755 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x8e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2002 : mword 11) ('b"0")), zreg)) codc_b755 exec_execute_C_J. Qed.

  (* --- the two [return 0] exits ---------------------------------------- *)

  Lemma coi_90 : COP 0x90 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* li    a0,0 -- the len == 0 exit *)
  Proof. mk_rvc (KernelSyms.copyout + 0x90)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x90) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma coi_92 : COP 0x92 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)).  (* j     +0x9a -- -> +0x9a, the pop *)
  Proof. mk_rvc (KernelSyms.copyout + 0x92)%Z (mword_of_int 0xa021 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x92) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 4 : mword 11) ('b"0")), zreg)) cdec_a021 exec_execute_C_J. Qed.

  Lemma coi_94 : COP 0x94 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* li    a0,0 -- the n == 0 exit: no frame to pop *)
  Proof. mk_rvc (KernelSyms.copyout + 0x94)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x94) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma coi_96 : COP 0x96 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.copyout + 0x96)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x96) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the -1 exit and the common 96-byte epilogue --------------------- *)

  Lemma coi_98 : COP 0x98 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* li    a0,-1 -- the va0 > MAXVA-1 exit *)
  Proof. mk_rvc (KernelSyms.copyout + 0x98)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x98) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma coi_9a : COP 0x9a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* ld    ra,88(sp) -- <- THE COMMON EPILOGUE (four arms) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x9a)%Z (mword_of_int 0x60e6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x9a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e6 exec_execute_C_LDSP. Qed.

  Lemma coi_9c : COP 0x9c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* ld    s0,80(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x9c)%Z (mword_of_int 0x6446 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x9c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6446 exec_execute_C_LDSP. Qed.

  Lemma coi_9e : COP 0x9e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* ld    s1,72(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0x9e)%Z (mword_of_int 0x64a6 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0x9e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a6 exec_execute_C_LDSP. Qed.

  Lemma coi_a0 : COP 0xa0 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* ld    s2,64(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xa0)%Z (mword_of_int 0x6906 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xa0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6906 exec_execute_C_LDSP. Qed.

  Lemma coi_a2 : COP 0xa2 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).  (* ld    s3,56(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xa2)%Z (mword_of_int 0x79e2 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xa2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79e2 exec_execute_C_LDSP. Qed.

  Lemma coi_a4 : COP 0xa4 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).  (* ld    s4,48(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xa4)%Z (mword_of_int 0x7a42 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xa4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a42 exec_execute_C_LDSP. Qed.

  Lemma coi_a6 : COP 0xa6 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).  (* ld    s5,40(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xa6)%Z (mword_of_int 0x7aa2 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xa6) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_7aa2 exec_execute_C_LDSP. Qed.

  Lemma coi_a8 : COP 0xa8 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).  (* ld    s6,32(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xa8)%Z (mword_of_int 0x7b02 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xa8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_7b02 exec_execute_C_LDSP. Qed.

  Lemma coi_aa : COP 0xaa true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).  (* ld    s7,24(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xaa)%Z (mword_of_int 0x6be2 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xaa) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6be2 exec_execute_C_LDSP. Qed.

  Lemma coi_ac : COP 0xac true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).  (* ld    s8,16(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xac)%Z (mword_of_int 0x6c42 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xac) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) cdec_6c42 exec_execute_C_LDSP. Qed.

  Lemma coi_ae : COP 0xae true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).  (* ld    s9,8(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xae)%Z (mword_of_int 0x6ca2 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xae) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) cdec_6ca2 exec_execute_C_LDSP. Qed.

  Lemma coi_b0 : COP 0xb0 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)).  (* ld    s10,0(sp) *)
  Proof. mk_rvc (KernelSyms.copyout + 0xb0)%Z (mword_of_int 0x6d02 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xb0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 26), false, 8)) codc_6d02 exec_execute_C_LDSP. Qed.

  Lemma coi_b2 : COP 0xb2 true (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)).  (* addi  sp,sp,96 *)
  Proof. mk_rvc (KernelSyms.copyout + 0xb2)%Z (mword_of_int 0x6125 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xb2) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)) cdec_6125 exec_execute_C_ADDI16SP. Qed.

  Lemma coi_b4 : COP 0xb4 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* ret *)
  Proof. mk_rvc (KernelSyms.copyout + 0xb4)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xb4) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the two remaining -1 exits, each rejoining the epilogue --------- *)

  Lemma coi_b6 : COP 0xb6 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* li    a0,-1 -- the vmfault-failed exit *)
  Proof. mk_rvc (KernelSyms.copyout + 0xb6)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xb6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma coi_b8 : COP 0xb8 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)).  (* j     +0x9a -- -> +0x9a *)
  Proof. mk_rvc (KernelSyms.copyout + 0xb8)%Z (mword_of_int 0xb7cd : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xb8) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2033 : mword 11) ('b"0")), zreg)) cdec_b7cd exec_execute_C_J. Qed.

  Lemma coi_ba : COP 0xba true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* li    a0,-1 -- the not-writable exit *)
  Proof. mk_rvc (KernelSyms.copyout + 0xba)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xba) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma coi_bc : COP 0xbc true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).  (* j     +0x9a -- -> +0x9a *)
  Proof. mk_rvc (KernelSyms.copyout + 0xbc)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (KernelSyms.copyout + 0xbc) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

End CopyoutInstrs.

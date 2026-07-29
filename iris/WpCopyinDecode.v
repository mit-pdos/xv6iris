(* WpCopyinDecode.v -- the instruction-DECODE layer for xv6's copyin().

     copyin @ 0x800016e2 .. 0x80001775   (offsets 0x00 .. 0x92, 63 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([cii_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the eleven 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>] -- including the whole 96-byte-frame push/pop set (0x711d ..
   0x1080 and 0x60e6 .. 0x6125), which copyin shares verbatim with copyout,
   plus 0x6b05 (also proc_mapstacks +0x48), 0x8baa / 0x855e (also copyout) and
   0x557d / 0x4501 / 0x8082.  copyin's own words are local, named
   [cidc_<word>] (compressed) / [cidb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which is stale by 14 bytes; the C is kernel/vm.c's
   user-to-kernel copy loop, one page-sized chunk per iteration):

     0x00 cac1     c.beqz a3,+0x90    # nbytes == 0 -> return 0
     0x02 711d     c.addi16sp sp,-96  # 96-byte frame: ra/s0/s1/s2..s9
     0x04 ec86     c.sdsp ra,88(sp)
     0x06 e8a2     c.sdsp s0,80(sp)
     0x08 e4a6     c.sdsp s1,72(sp)
     0x0a e0ca     c.sdsp s2,64(sp)
     0x0c fc4e     c.sdsp s3,56(sp)
     0x0e f852     c.sdsp s4,48(sp)
     0x10 f456     c.sdsp s5,40(sp)
     0x12 f05a     c.sdsp s6,32(sp)
     0x14 ec5e     c.sdsp s7,24(sp)
     0x16 e862     c.sdsp s8,16(sp)
     0x18 e466     c.sdsp s9,8(sp)
     0x1a 1080     c.addi4spn s0,sp,96
     0x1c 8baa     c.mv s7,a0         # s7 := pagetable
     0x1e 8aae     c.mv s5,a1         # s5 := dst
     0x20 8932     c.mv s2,a2         # s2 := srcva
     0x22 8a36     c.mv s4,a3         # s4 := len
     0x24 7c7d     c.lui s8,0xfffff   # s8 := -4096 (PGROUNDDOWN mask)
     0x26 4c85     c.li s9,1          # s9 := 1 (walkaddr's user flag)
     0x28 6b05     c.lui s6,0x1       # s6 := PGSIZE
     0x2a a035     c.j +0x56          # enter the loop at the walkaddr probe
     0x2c 412984b3 sub s1,s3,s2       # s1 := va0 + PGSIZE - srcva
     0x30 94da     c.add s1,s1,s6
     0x32 009a7363 bgeu s4,s1,+0x38   # n = min(s1, len)
     0x36 84d2     c.mv s1,s4
     0x38 413905b3 sub a1,s2,s3       # a1 := srcva - va0
     0x3c 0004861b sext.w a2,s1       # a2 := (int)n
     0x40 95aa     c.add a1,a1,a0     # a1 := pa0 + (srcva - va0)
     0x42 8556     c.mv a0,s5         # a0 := dst
     0x44 e02ff0ef jal ra,memmove     # -2558 -> 0x80000d28
     0x48 409a0a33 sub s4,s4,s1       # len -= n
     0x4c 9aa6     c.add s5,s5,s1     # dst += n
     0x4e 01698933 add s2,s3,s6       # srcva := va0 + PGSIZE
     0x52 020a0163 beqz s4,+0x74      # len == 0 -> return 0
     0x56 018979b3 and s3,s2,s8       # s3 := va0 = PGROUNDDOWN(srcva)
     0x5a 85ce     c.mv a1,s3
     0x5c 855e     c.mv a0,s7
     0x5e 8b7ff0ef jal ra,walkaddr    # -1866 -> 0x80000ff6
     0x62 f569     c.bnez a0,-0x36    # -> +0x2c, mapped: copy this chunk
     0x64 8666     c.mv a2,s9         # vmfault read = 1
     0x66 85ce     c.mv a1,s3
     0x68 855e     c.mv a0,s7
     0x6a e55ff0ef jal ra,vmfault     # -428 -> 0x800015a0
     0x6e fd5d     c.bnez a0,-0x42    # -> +0x2c, faulted in: copy
     0x70 557d     c.li a0,-1         # unmapped and unfaultable
     0x72 a011     c.j +0x76
     0x74 4501     c.li a0,0          # the success return
     0x76 60e6     c.ldsp ra,88(sp)
     0x78 6446     c.ldsp s0,80(sp)
     0x7a 64a6     c.ldsp s1,72(sp)
     0x7c 6906     c.ldsp s2,64(sp)
     0x7e 79e2     c.ldsp s3,56(sp)
     0x80 7a42     c.ldsp s4,48(sp)
     0x82 7aa2     c.ldsp s5,40(sp)
     0x84 7b02     c.ldsp s6,32(sp)
     0x86 6be2     c.ldsp s7,24(sp)
     0x88 6c42     c.ldsp s8,16(sp)
     0x8a 6ca2     c.ldsp s9,8(sp)
     0x8c 6125     c.addi16sp sp,96
     0x8e 8082     c.ret
     0x90 4501     c.li a0,0          # nbytes == 0: nothing to copy
     0x92 8082     c.ret

   The loop is entered at its bottom (the [c.j +0x56] at 0x2a), so 0x56..0x6e
   is the head -- PGROUNDDOWN the cursor, walkaddr the page, and on a miss let
   vmfault map it -- and 0x2c..0x52 the body that memmoves min(len, page tail)
   bytes and advances.  Two arms reach the body (0x62 after walkaddr, 0x6e
   after vmfault); the [c.li a0,-1] at 0x70 is the give-up return and falls
   into the shared epilogue via 0x72, which the loop's own [beqz s4] exit at
   0x52 reaches through 0x74.  The [nbytes == 0] test at 0x00 skips the frame
   entirely and returns 0 out of 0x90/0x92 -- a second, frameless [c.ret].

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.bnez]s are 229 / 223 (2^8 complements of -27 / -33 half-words)
   and the [jal]s are 2094594 / 2095286 / 2096724 (2^21 complements of the
   byte offsets -2558 / -1866 / -428 to memmove / walkaddr / vmfault).       *)
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
(* Compressed decode facts for copyin's own words.                        *)
(* ===================================================================== *)

(* 0x00  c.beqz a3,+0x90 *)
Lemma cidc_cac1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcac1 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 72, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1e  c.mv s5,a1 *)
Lemma cidc_8aae s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8aae : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x20  c.mv s2,a2 *)
Lemma cidc_8932 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8932 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 18), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x22  c.mv s4,a3 *)
Lemma cidc_8a36 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8a36 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x24  c.lui s8,0xfffff *)
Lemma cidc_7c7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7c7d : mword 16)) s
  = Some (C_LUI (mword_of_int 63, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x26  c.li s9,1 *)
Lemma cidc_4c85 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4c85 : mword 16)) s
  = Some (C_LI (mword_of_int 1, Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2a  c.j +0x56 *)
Lemma cidc_a035 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa035 : mword 16)) s
  = Some (C_J (mword_of_int 22), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x30  c.add s1,s1,s6 *)
Lemma cidc_94da s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x94da : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 9), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x36  c.mv s1,s4 *)
Lemma cidc_84d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x84d2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 9), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x40  c.add a1,a1,a0 *)
Lemma cidc_95aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x95aa : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 11), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x42  c.mv a0,s5 *)
(* [cdec_8556] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x4c  c.add s5,s5,s1 *)
Lemma cidc_9aa6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9aa6 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 21), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x5a / 0x66  c.mv a1,s3 *)
Lemma cidc_85ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85ce : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x62  c.bnez a0,-0x36 *)
Lemma cidc_f569 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf569 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 229, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64  c.mv a2,s9 *)
Lemma cidc_8666 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8666 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 25)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6e  c.bnez a0,-0x42 *)
Lemma cidc_fd5d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfd5d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 223, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x72  c.j +0x76 *)
Lemma cidc_a011 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa011 : mword 16)) s
  = Some (C_J (mword_of_int 2), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all eleven are copyin's own.             *)
(* ===================================================================== *)

(* 0x2c  sub s1,s3,s2       # s1 := va0 + PGSIZE - srcva *)
Lemma cidb_412984b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x412984b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 19), Regidx (mword_of_int 9), SUB), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  bgeu s4,s1,+0x38   # n = min(s1, len) *)
Lemma cidb_009a7363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x009a7363 : mword 32)) s
  = Some (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 20), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x38  sub a1,s2,s3       # a1 := srcva - va0 *)
Lemma cidb_413905b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x413905b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 18), Regidx (mword_of_int 11), SUB), s).
Proof. decode_bridge_ms. Qed.

(* 0x3c  sext.w a2,s1       # a2 := (int)n *)
Lemma cidb_0004861b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004861b : mword 32)) s
  = Some (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 12)), s).
Proof. decode_bridge_ms. Qed.

(* 0x44  jal ra,memmove     # -2558 -> 0x80000d28 *)
Lemma cidb_e02ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe02ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094594 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  sub s4,s4,s1       # len -= n *)
Lemma cidb_409a0a33 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x409a0a33 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 20), SUB), s).
Proof. decode_bridge_ms. Qed.

(* 0x4e  add s2,s3,s6       # srcva := va0 + PGSIZE *)
Lemma cidb_01698933 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01698933 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 19), Regidx (mword_of_int 18), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x52  beqz s4,+0x74      # len == 0 -> return 0 *)
Lemma cidb_020a0163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020a0163 : mword 32)) s
  = Some (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x56  and s3,s2,s8       # s3 := va0 = PGROUNDDOWN(srcva) *)
Lemma cidb_018979b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x018979b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 18), Regidx (mword_of_int 19), AND), s).
Proof. decode_bridge_ms. Qed.

(* 0x5e  jal ra,walkaddr    # -1866 -> 0x80000ff6 *)
Lemma cidb_8b7ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8b7ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095286 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x6a  jal ra,vmfault     # -428 -> 0x800015a0 *)
Lemma cidb_e55ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe55ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096724 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section CopyinInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation CI := KernelSyms.copyin.

  (* --- the nbytes == 0 short circuit and the prologue --------------- *)

  Lemma cii_00 : kernel_text -∗ instr (mword_of_int (CI + 0x00) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 72 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)).  (* c.beqz a3,+0x90    # nbytes == 0 -> return 0 *)
  Proof. mk_rvc (CI + 0x00)%Z (mword_of_int 0xcac1 : mword 16)
    (mword_of_int (CI + 0x00) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 72 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)) cidc_cac1 exec_execute_C_BEQZ. Qed.

  Lemma cii_02 : kernel_text -∗ instr (mword_of_int (CI + 0x02) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,-96  # 96-byte frame: ra/s0/s1/s2..s9 *)
  Proof. mk_rvc (CI + 0x02)%Z (mword_of_int 0x711d : mword 16)
    (mword_of_int (CI + 0x02) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)) cdec_711d exec_execute_C_ADDI16SP. Qed.

  Lemma cii_04 : kernel_text -∗ instr (mword_of_int (CI + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,88(sp) *)
  Proof. mk_rvc (CI + 0x04)%Z (mword_of_int 0xec86 : mword 16)
    (mword_of_int (CI + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec86 exec_execute_C_SDSP. Qed.

  Lemma cii_06 : kernel_text -∗ instr (mword_of_int (CI + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,80(sp) *)
  Proof. mk_rvc (CI + 0x06)%Z (mword_of_int 0xe8a2 : mword 16)
    (mword_of_int (CI + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e8a2 exec_execute_C_SDSP. Qed.

  Lemma cii_08 : kernel_text -∗ instr (mword_of_int (CI + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* c.sdsp s1,72(sp) *)
  Proof. mk_rvc (CI + 0x08)%Z (mword_of_int 0xe4a6 : mword 16)
    (mword_of_int (CI + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e4a6 exec_execute_C_SDSP. Qed.

  Lemma cii_0a : kernel_text -∗ instr (mword_of_int (CI + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* c.sdsp s2,64(sp) *)
  Proof. mk_rvc (CI + 0x0a)%Z (mword_of_int 0xe0ca : mword 16)
    (mword_of_int (CI + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e0ca exec_execute_C_SDSP. Qed.

  Lemma cii_0c : kernel_text -∗ instr (mword_of_int (CI + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).  (* c.sdsp s3,56(sp) *)
  Proof. mk_rvc (CI + 0x0c)%Z (mword_of_int 0xfc4e : mword 16)
    (mword_of_int (CI + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_fc4e exec_execute_C_SDSP. Qed.

  Lemma cii_0e : kernel_text -∗ instr (mword_of_int (CI + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).  (* c.sdsp s4,48(sp) *)
  Proof. mk_rvc (CI + 0x0e)%Z (mword_of_int 0xf852 : mword 16)
    (mword_of_int (CI + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f852 exec_execute_C_SDSP. Qed.

  Lemma cii_10 : kernel_text -∗ instr (mword_of_int (CI + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).  (* c.sdsp s5,40(sp) *)
  Proof. mk_rvc (CI + 0x10)%Z (mword_of_int 0xf456 : mword 16)
    (mword_of_int (CI + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_f456 exec_execute_C_SDSP. Qed.

  Lemma cii_12 : kernel_text -∗ instr (mword_of_int (CI + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).  (* c.sdsp s6,32(sp) *)
  Proof. mk_rvc (CI + 0x12)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (CI + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  Lemma cii_14 : kernel_text -∗ instr (mword_of_int (CI + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).  (* c.sdsp s7,24(sp) *)
  Proof. mk_rvc (CI + 0x14)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (CI + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  Lemma cii_16 : kernel_text -∗ instr (mword_of_int (CI + 0x16) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).  (* c.sdsp s8,16(sp) *)
  Proof. mk_rvc (CI + 0x16)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (CI + 0x16) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  Lemma cii_18 : kernel_text -∗ instr (mword_of_int (CI + 0x18) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)).  (* c.sdsp s9,8(sp) *)
  Proof. mk_rvc (CI + 0x18)%Z (mword_of_int 0xe466 : mword 16)
    (mword_of_int (CI + 0x18) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 25), sp, 8)) cdec_e466 exec_execute_C_SDSP. Qed.

  Lemma cii_1a : kernel_text -∗ instr (mword_of_int (CI + 0x1a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,96 *)
  Proof. mk_rvc (CI + 0x1a)%Z (mword_of_int 0x1080 : mword 16)
    (mword_of_int (CI + 0x1a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1080 exec_execute_C_ADDI4SPN. Qed.

  (* --- the loop-invariant registers ---------------------------------- *)

  Lemma cii_1c : kernel_text -∗ instr (mword_of_int (CI + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 23), ADD)).  (* c.mv s7,a0         # s7 := pagetable *)
  Proof. mk_rvc (CI + 0x1c)%Z (mword_of_int 0x8baa : mword 16)
    (mword_of_int (CI + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 23), ADD)) cdec_8baa exec_execute_C_MV. Qed.

  Lemma cii_1e : kernel_text -∗ instr (mword_of_int (CI + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 21), ADD)).  (* c.mv s5,a1         # s5 := dst *)
  Proof. mk_rvc (CI + 0x1e)%Z (mword_of_int 0x8aae : mword 16)
    (mword_of_int (CI + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 21), ADD)) cidc_8aae exec_execute_C_MV. Qed.

  Lemma cii_20 : kernel_text -∗ instr (mword_of_int (CI + 0x20) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 18), ADD)).  (* c.mv s2,a2         # s2 := srcva *)
  Proof. mk_rvc (CI + 0x20)%Z (mword_of_int 0x8932 : mword 16)
    (mword_of_int (CI + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 18), ADD)) cidc_8932 exec_execute_C_MV. Qed.

  Lemma cii_22 : kernel_text -∗ instr (mword_of_int (CI + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 20), ADD)).  (* c.mv s4,a3         # s4 := len *)
  Proof. mk_rvc (CI + 0x22)%Z (mword_of_int 0x8a36 : mword 16)
    (mword_of_int (CI + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 20), ADD)) cidc_8a36 exec_execute_C_MV. Qed.

  Lemma cii_24 : kernel_text -∗ instr (mword_of_int (CI + 0x24) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 24), LUI)).  (* c.lui s8,0xfffff   # s8 := -4096 (PGROUNDDOWN mask) *)
  Proof. mk_rvc (CI + 0x24)%Z (mword_of_int 0x7c7d : mword 16)
    (mword_of_int (CI + 0x24) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 24), LUI)) cidc_7c7d exec_execute_C_LUI. Qed.

  Lemma cii_26 : kernel_text -∗ instr (mword_of_int (CI + 0x26) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 25), ADDI)).  (* c.li s9,1          # s9 := 1 (walkaddr's user flag) *)
  Proof. mk_rvc (CI + 0x26)%Z (mword_of_int 0x4c85 : mword 16)
    (mword_of_int (CI + 0x26) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 25), ADDI)) cidc_4c85 exec_execute_C_LI. Qed.

  Lemma cii_28 : kernel_text -∗ instr (mword_of_int (CI + 0x28) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)).  (* c.lui s6,0x1       # s6 := PGSIZE *)
  Proof. mk_rvc (CI + 0x28)%Z (mword_of_int 0x6b05 : mword 16)
    (mword_of_int (CI + 0x28) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)) cdec_6b05 exec_execute_C_LUI. Qed.

  Lemma cii_2a : kernel_text -∗ instr (mword_of_int (CI + 0x2a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")), zreg)).  (* c.j +0x56          # enter the loop at the walkaddr probe *)
  Proof. mk_rvc (CI + 0x2a)%Z (mword_of_int 0xa035 : mword 16)
    (mword_of_int (CI + 0x2a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 22 : mword 11) ('b"0")), zreg)) cidc_a035 exec_execute_C_J. Qed.

  (* --- loop body: n = min(len, va0+PGSIZE-srcva), memmove, advance --- *)

  Lemma cii_2c : kernel_text -∗ instr (mword_of_int (CI + 0x2c) : mword 64) false (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 19), Regidx (mword_of_int 9), SUB)).  (* sub s1,s3,s2       # s1 := va0 + PGSIZE - srcva *)
  Proof. mk_base (CI + 0x2c)%Z (mword_of_int 0x412984b3 : mword 32)
    (mword_of_int (CI + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 19), Regidx (mword_of_int 9), SUB)) cidb_412984b3. Qed.

  Lemma cii_30 : kernel_text -∗ instr (mword_of_int (CI + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)).  (* c.add s1,s1,s6 *)
  Proof. mk_rvc (CI + 0x30)%Z (mword_of_int 0x94da : mword 16)
    (mword_of_int (CI + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADD)) cidc_94da exec_execute_C_ADD. Qed.

  Lemma cii_32 : kernel_text -∗ instr (mword_of_int (CI + 0x32) : mword 64) false (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 20), BGEU)).  (* bgeu s4,s1,+0x38   # n = min(s1, len) *)
  Proof. mk_base (CI + 0x32)%Z (mword_of_int 0x009a7363 : mword 32)
    (mword_of_int (CI + 0x32) : mword 64) (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 20), BGEU)) cidb_009a7363. Qed.

  Lemma cii_36 : kernel_text -∗ instr (mword_of_int (CI + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,s4 *)
  Proof. mk_rvc (CI + 0x36)%Z (mword_of_int 0x84d2 : mword 16)
    (mword_of_int (CI + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 9), ADD)) cidc_84d2 exec_execute_C_MV. Qed.

  Lemma cii_38 : kernel_text -∗ instr (mword_of_int (CI + 0x38) : mword 64) false (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 18), Regidx (mword_of_int 11), SUB)).  (* sub a1,s2,s3       # a1 := srcva - va0 *)
  Proof. mk_base (CI + 0x38)%Z (mword_of_int 0x413905b3 : mword 32)
    (mword_of_int (CI + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 19), Regidx (mword_of_int 18), Regidx (mword_of_int 11), SUB)) cidb_413905b3. Qed.

  Lemma cii_3c : kernel_text -∗ instr (mword_of_int (CI + 0x3c) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 12))).  (* sext.w a2,s1       # a2 := (int)n *)
  Proof. mk_base (CI + 0x3c)%Z (mword_of_int 0x0004861b : mword 32)
    (mword_of_int (CI + 0x3c) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 12))) cidb_0004861b. Qed.

  Lemma cii_40 : kernel_text -∗ instr (mword_of_int (CI + 0x40) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)).  (* c.add a1,a1,a0     # a1 := pa0 + (srcva - va0) *)
  Proof. mk_rvc (CI + 0x40)%Z (mword_of_int 0x95aa : mword 16)
    (mword_of_int (CI + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)) cidc_95aa exec_execute_C_ADD. Qed.

  Lemma cii_42 : kernel_text -∗ instr (mword_of_int (CI + 0x42) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s5         # a0 := dst *)
  Proof. mk_rvc (CI + 0x42)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (CI + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) cdec_8556 exec_execute_C_MV. Qed.

  Lemma cii_44 : kernel_text -∗ instr (mword_of_int (CI + 0x44) : mword 64) false (JAL (mword_of_int 2094594 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,memmove     # -2558 -> 0x80000d28 *)
  Proof. mk_base (CI + 0x44)%Z (mword_of_int 0xe02ff0ef : mword 32)
    (mword_of_int (CI + 0x44) : mword 64) (JAL (mword_of_int 2094594 : mword 21, Regidx (mword_of_int 1))) cidb_e02ff0ef. Qed.

  Lemma cii_48 : kernel_text -∗ instr (mword_of_int (CI + 0x48) : mword 64) false (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 20), SUB)).  (* sub s4,s4,s1       # len -= n *)
  Proof. mk_base (CI + 0x48)%Z (mword_of_int 0x409a0a33 : mword 32)
    (mword_of_int (CI + 0x48) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 20), Regidx (mword_of_int 20), SUB)) cidb_409a0a33. Qed.

  Lemma cii_4c : kernel_text -∗ instr (mword_of_int (CI + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADD)).  (* c.add s5,s5,s1     # dst += n *)
  Proof. mk_rvc (CI + 0x4c)%Z (mword_of_int 0x9aa6 : mword 16)
    (mword_of_int (CI + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 21), Regidx (mword_of_int 21), ADD)) cidc_9aa6 exec_execute_C_ADD. Qed.

  Lemma cii_4e : kernel_text -∗ instr (mword_of_int (CI + 0x4e) : mword 64) false (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 19), Regidx (mword_of_int 18), ADD)).  (* add s2,s3,s6       # srcva := va0 + PGSIZE *)
  Proof. mk_base (CI + 0x4e)%Z (mword_of_int 0x01698933 : mword 32)
    (mword_of_int (CI + 0x4e) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 19), Regidx (mword_of_int 18), ADD)) cidb_01698933. Qed.

  Lemma cii_52 : kernel_text -∗ instr (mword_of_int (CI + 0x52) : mword 64) false (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ)).  (* beqz s4,+0x74      # len == 0 -> return 0 *)
  Proof. mk_base (CI + 0x52)%Z (mword_of_int 0x020a0163 : mword 32)
    (mword_of_int (CI + 0x52) : mword 64) (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 20), BEQ)) cidb_020a0163. Qed.

  (* --- loop head: PGROUNDDOWN, walkaddr, and the vmfault retry ------- *)

  Lemma cii_56 : kernel_text -∗ instr (mword_of_int (CI + 0x56) : mword 64) false (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 18), Regidx (mword_of_int 19), AND)).  (* and s3,s2,s8       # s3 := va0 = PGROUNDDOWN(srcva) *)
  Proof. mk_base (CI + 0x56)%Z (mword_of_int 0x018979b3 : mword 32)
    (mword_of_int (CI + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 24), Regidx (mword_of_int 18), Regidx (mword_of_int 19), AND)) cidb_018979b3. Qed.

  Lemma cii_5a : kernel_text -∗ instr (mword_of_int (CI + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s3 *)
  Proof. mk_rvc (CI + 0x5a)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (CI + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) cidc_85ce exec_execute_C_MV. Qed.

  Lemma cii_5c : kernel_text -∗ instr (mword_of_int (CI + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s7 *)
  Proof. mk_rvc (CI + 0x5c)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (CI + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma cii_5e : kernel_text -∗ instr (mword_of_int (CI + 0x5e) : mword 64) false (JAL (mword_of_int 2095286 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,walkaddr    # -1866 -> 0x80000ff6 *)
  Proof. mk_base (CI + 0x5e)%Z (mword_of_int 0x8b7ff0ef : mword 32)
    (mword_of_int (CI + 0x5e) : mword 64) (JAL (mword_of_int 2095286 : mword 21, Regidx (mword_of_int 1))) cidb_8b7ff0ef. Qed.

  Lemma cii_62 : kernel_text -∗ instr (mword_of_int (CI + 0x62) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 229 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).  (* c.bnez a0,-0x36    # -> +0x2c, mapped: copy this chunk *)
  Proof. mk_rvc (CI + 0x62)%Z (mword_of_int 0xf569 : mword 16)
    (mword_of_int (CI + 0x62) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 229 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) cidc_f569 exec_execute_C_BNEZ. Qed.

  Lemma cii_64 : kernel_text -∗ instr (mword_of_int (CI + 0x64) : mword 64) true (RTYPE (Regidx (mword_of_int 25), zreg, Regidx (mword_of_int 12), ADD)).  (* c.mv a2,s9         # vmfault read = 1 *)
  Proof. mk_rvc (CI + 0x64)%Z (mword_of_int 0x8666 : mword 16)
    (mword_of_int (CI + 0x64) : mword 64) (RTYPE (Regidx (mword_of_int 25), zreg, Regidx (mword_of_int 12), ADD)) cidc_8666 exec_execute_C_MV. Qed.

  Lemma cii_66 : kernel_text -∗ instr (mword_of_int (CI + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s3 *)
  Proof. mk_rvc (CI + 0x66)%Z (mword_of_int 0x85ce : mword 16)
    (mword_of_int (CI + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 11), ADD)) cidc_85ce exec_execute_C_MV. Qed.

  Lemma cii_68 : kernel_text -∗ instr (mword_of_int (CI + 0x68) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s7 *)
  Proof. mk_rvc (CI + 0x68)%Z (mword_of_int 0x855e : mword 16)
    (mword_of_int (CI + 0x68) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 10), ADD)) cdec_855e exec_execute_C_MV. Qed.

  Lemma cii_6a : kernel_text -∗ instr (mword_of_int (CI + 0x6a) : mword 64) false (JAL (mword_of_int 2096724 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,vmfault     # -428 -> 0x800015a0 *)
  Proof. mk_base (CI + 0x6a)%Z (mword_of_int 0xe55ff0ef : mword 32)
    (mword_of_int (CI + 0x6a) : mword 64) (JAL (mword_of_int 2096724 : mword 21, Regidx (mword_of_int 1))) cidb_e55ff0ef. Qed.

  Lemma cii_6e : kernel_text -∗ instr (mword_of_int (CI + 0x6e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 223 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).  (* c.bnez a0,-0x42    # -> +0x2c, faulted in: copy *)
  Proof. mk_rvc (CI + 0x6e)%Z (mword_of_int 0xfd5d : mword 16)
    (mword_of_int (CI + 0x6e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 223 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) cidc_fd5d exec_execute_C_BNEZ. Qed.

  (* --- the two returns and the shared epilogue ----------------------- *)

  Lemma cii_70 : kernel_text -∗ instr (mword_of_int (CI + 0x70) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,-1         # unmapped and unfaultable *)
  Proof. mk_rvc (CI + 0x70)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (CI + 0x70) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma cii_72 : kernel_text -∗ instr (mword_of_int (CI + 0x72) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)).  (* c.j +0x76 *)
  Proof. mk_rvc (CI + 0x72)%Z (mword_of_int 0xa011 : mword 16)
    (mword_of_int (CI + 0x72) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2 : mword 11) ('b"0")), zreg)) cidc_a011 exec_execute_C_J. Qed.

  Lemma cii_74 : kernel_text -∗ instr (mword_of_int (CI + 0x74) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,0          # the success return *)
  Proof. mk_rvc (CI + 0x74)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (CI + 0x74) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma cii_76 : kernel_text -∗ instr (mword_of_int (CI + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,88(sp) *)
  Proof. mk_rvc (CI + 0x76)%Z (mword_of_int 0x60e6 : mword 16)
    (mword_of_int (CI + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e6 exec_execute_C_LDSP. Qed.

  Lemma cii_78 : kernel_text -∗ instr (mword_of_int (CI + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,80(sp) *)
  Proof. mk_rvc (CI + 0x78)%Z (mword_of_int 0x6446 : mword 16)
    (mword_of_int (CI + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6446 exec_execute_C_LDSP. Qed.

  Lemma cii_7a : kernel_text -∗ instr (mword_of_int (CI + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* c.ldsp s1,72(sp) *)
  Proof. mk_rvc (CI + 0x7a)%Z (mword_of_int 0x64a6 : mword 16)
    (mword_of_int (CI + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a6 exec_execute_C_LDSP. Qed.

  Lemma cii_7c : kernel_text -∗ instr (mword_of_int (CI + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* c.ldsp s2,64(sp) *)
  Proof. mk_rvc (CI + 0x7c)%Z (mword_of_int 0x6906 : mword 16)
    (mword_of_int (CI + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6906 exec_execute_C_LDSP. Qed.

  Lemma cii_7e : kernel_text -∗ instr (mword_of_int (CI + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).  (* c.ldsp s3,56(sp) *)
  Proof. mk_rvc (CI + 0x7e)%Z (mword_of_int 0x79e2 : mword 16)
    (mword_of_int (CI + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79e2 exec_execute_C_LDSP. Qed.

  Lemma cii_80 : kernel_text -∗ instr (mword_of_int (CI + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).  (* c.ldsp s4,48(sp) *)
  Proof. mk_rvc (CI + 0x80)%Z (mword_of_int 0x7a42 : mword 16)
    (mword_of_int (CI + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a42 exec_execute_C_LDSP. Qed.

  Lemma cii_82 : kernel_text -∗ instr (mword_of_int (CI + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).  (* c.ldsp s5,40(sp) *)
  Proof. mk_rvc (CI + 0x82)%Z (mword_of_int 0x7aa2 : mword 16)
    (mword_of_int (CI + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_7aa2 exec_execute_C_LDSP. Qed.

  Lemma cii_84 : kernel_text -∗ instr (mword_of_int (CI + 0x84) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).  (* c.ldsp s6,32(sp) *)
  Proof. mk_rvc (CI + 0x84)%Z (mword_of_int 0x7b02 : mword 16)
    (mword_of_int (CI + 0x84) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_7b02 exec_execute_C_LDSP. Qed.

  Lemma cii_86 : kernel_text -∗ instr (mword_of_int (CI + 0x86) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).  (* c.ldsp s7,24(sp) *)
  Proof. mk_rvc (CI + 0x86)%Z (mword_of_int 0x6be2 : mword 16)
    (mword_of_int (CI + 0x86) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6be2 exec_execute_C_LDSP. Qed.

  Lemma cii_88 : kernel_text -∗ instr (mword_of_int (CI + 0x88) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).  (* c.ldsp s8,16(sp) *)
  Proof. mk_rvc (CI + 0x88)%Z (mword_of_int 0x6c42 : mword 16)
    (mword_of_int (CI + 0x88) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) cdec_6c42 exec_execute_C_LDSP. Qed.

  Lemma cii_8a : kernel_text -∗ instr (mword_of_int (CI + 0x8a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)).  (* c.ldsp s9,8(sp) *)
  Proof. mk_rvc (CI + 0x8a)%Z (mword_of_int 0x6ca2 : mword 16)
    (mword_of_int (CI + 0x8a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 25), false, 8)) cdec_6ca2 exec_execute_C_LDSP. Qed.

  Lemma cii_8c : kernel_text -∗ instr (mword_of_int (CI + 0x8c) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,96 *)
  Proof. mk_rvc (CI + 0x8c)%Z (mword_of_int 0x6125 : mword 16)
    (mword_of_int (CI + 0x8c) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)) cdec_6125 exec_execute_C_ADDI16SP. Qed.

  Lemma cii_8e : kernel_text -∗ instr (mword_of_int (CI + 0x8e) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (CI + 0x8e)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (CI + 0x8e) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the frameless nbytes == 0 return ------------------------------ *)

  Lemma cii_90 : kernel_text -∗ instr (mword_of_int (CI + 0x90) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,0          # nbytes == 0: nothing to copy *)
  Proof. mk_rvc (CI + 0x90)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (CI + 0x90) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma cii_92 : kernel_text -∗ instr (mword_of_int (CI + 0x92) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (CI + 0x92)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (CI + 0x92) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CopyinInstrs.

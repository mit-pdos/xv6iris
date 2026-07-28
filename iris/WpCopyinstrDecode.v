(* WpCopyinstrDecode.v -- the instruction-DECODE layer for xv6's copyinstr().

     copyinstr @ 0x800014c8 .. 0x80001583   (offsets 0x00 .. 0xba, 188 bytes)

   For every instruction the function can REACH it proves a
   [kernel_text -* instr pc <is_rvc> <AST>] fact ([csi_<off>]) plus the
   per-instruction decode facts they consume -- [mk_rvc] for the compressed
   words, [mk_base] for the seventeen 4-byte ones.  Words the rest of the tree
   already decodes come from KernelRvcDecode as [cdec_<word>] (the whole
   80-byte-frame push/pop set is new here but its individual [c.sdsp]/[c.ldsp]
   words are shared with other frames); copyinstr's own words are local, named
   [csdc_<word>] (compressed) / [csdb_<word>] (base).

   +0xa8 .. +0xae IS DEAD CODE and deliberately absent.  It is the [n == 0]
   arm of the [c.beqz a3] at +0x78, and [n = min(PGSIZE - off, max)] with
   [max >= 1] and [off < PGSIZE] is never 0 -- the proof discharges that
   branch as not-taken, so those four instructions are never decoded.  (The
   +0x78 test itself IS here: proving the branch dead still requires
   executing it.)

   THE SHAPE OF THE FUNCTION.  Two nested loops and four exits:

     +0x00                 max == 0 -> +0xb0, return -1 with NO frame
     +0x02..+0x22          the 80-byte (10-slot) prologue and
                           s5=pagetable s1=dst s7=srcva s3=max s6=-4096 s4=4096
     +0x24 j +0x5e         enter the OUTER loop at its head

     +0x5e and s2,s7,s6    va0 = PGROUNDDOWN(srcva)          <-- outer head
     +0x66 jal walkaddr
     +0x6a beqz a0 -> +0xa4        unmapped: return -1
     +0x6c..+0x76          n = min(PGSIZE - (srcva - va0), max)
     +0x78 beqz a3 -> +0xa8        dead
     +0x7a..+0x86          a2 = p - dst, a5 = dst, a3 = dst + n

     +0x88 mv a1,a5        <-- INNER head (one byte per iteration)
     +0x8e lbu a4,0(a4)
     +0x92 beqz a4 -> +0x26        the NUL: write it and return 0
     +0x94 sb a4,0(a5) ; +0x98 a5++
     +0x9a bne a5,a3 -> +0x88      more of this chunk
     +0x9e j +0x4a                 the chunk is done

     +0x4a..+0x58          max -= n, srcva = va0 + PGSIZE, and
                           beq a1,a4 -> +0xa0 when max hit 0 (return -1)
     +0x5c mv s1,a5        dst += n, fall through to the outer head

     +0x26..+0x30          *dst = 0 ; got_null = 1 ; a0 = -(got_null^1) = 0
     +0xa0..+0x30          got_null = 0 -> a0 = -1
     +0x34..+0x48          the 10-slot epilogue, reached by all three
                           frame-holding exits
     +0xb0..+0xba          the frameless max == 0 return

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.j]s are 2006 / 1989 / 1991 (2^11 complements of -42 / -59 / -57
   half-words), the backward [c.beqz] is 202, the [bne]'s 13-bit immediate is
   8174, and the [jal] to walkaddr is 2095816 (2^21 - 1336).                  *)
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
Require Import UserExecFacts.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for this function's own words.                 *)
(* ===================================================================== *)

(* c.beqz a3,+0xb0    # max == 0 -> return -1, no frame *)
Lemma csdc_cac5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcac5 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 88, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv s5,a0          # s5 := pagetable *)
Lemma csdc_8aaa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8aaa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv s7,a2          # s7 := srcva *)
Lemma csdc_8bb2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8bb2 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 23), Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv s3,a3          # s3 := max *)
Lemma csdc_89b6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x89b6 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 19), Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.lui s6,0xfffff    # s6 := -4096 (PGROUNDDOWN mask) *)
Lemma csdc_7b7d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7b7d : mword 16)) s
  = Some (C_LUI (mword_of_int 63, Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.lui s4,0x1        # s4 := PGSIZE *)
Lemma csdc_6a05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a05 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.j +0x5e           # enter the outer loop at its head *)
Lemma csdc_a82d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa82d : mword 16)) s
  = Some (C_J (mword_of_int 29), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.add a4,a4,s1      # a4 := dst_base + (rem-1) *)
Lemma csdc_9726 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9726 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a0,s5 *)
Lemma csdc_8556 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8556 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.beqz a0,+0xa4     # unmapped -> return -1 *)
Lemma csdc_cd0d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd0d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 29, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.add a3,a3,s4      # n := PGSIZE - (srcva - va0) *)
Lemma csdc_96d2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x96d2 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 13), Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a3,s3 *)
Lemma csdc_86ce s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x86ce : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 13), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.beqz a3,+0xa8     # DEAD: n >= 1 always *)
Lemma csdc_ca85 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xca85 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 24, Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a5,s1          # a5 := dst cursor *)
Lemma csdc_87a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x87a6 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 15), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.sub a2,a2,s1      # a2 := p - dst  (the source/dest delta) *)
Lemma csdc_8e05 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8e05 : mword 16)) s
  = Some (C_SUB (Cregidx (mword_of_int 4), Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.add a3,a3,s1      # a3 := dst + n  (the end pointer) *)
Lemma csdc_96a6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x96a6 : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 13), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.mv a1,a5          # <-- inner head; a1 records the cursor *)
Lemma csdc_85be s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85be : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.beqz a4,-0x6c     # -> +0x26, the NUL was found *)
Lemma csdc_db51 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdb51 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 202, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.addi a5,a5,1 *)
Lemma csdc_0785 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0785 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.j -0x54           # -> +0x4a, the chunk is done *)
Lemma csdc_b775 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb775 : mword 16)) s
  = Some (C_J (mword_of_int 2006), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.j -0x76           # -> +0x2c *)
Lemma csdc_b769 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb769 : mword 16)) s
  = Some (C_J (mword_of_int 1989), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* c.j -0x72           # -> +0x34, the epilogue *)
Lemma csdc_b779 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb779 : mword 16)) s
  = Some (C_J (mword_of_int 1991), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* sb zero,0(a5)       # *dst = '\0' *)
Lemma csdb_00078023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00078023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* xori a5,a5,1        # a5 := !got_null *)
Lemma csdb_0017c793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017c793 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), XORI), s).
Proof. decode_bridge_ms. Qed.

(* negw a0,a5          # 0 -> 0, 1 -> -1 *)
Lemma csdb_40f0053b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40f0053b : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* addi a4,s3,-1       # a4 := rem - 1 *)
Lemma csdb_fff98713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfff98713 : mword 32)) s
  = Some (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* sub s3,a4,a1        # max -= n *)
Lemma csdb_40b709b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x40b709b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 14), Regidx (mword_of_int 19), SUB), s).
Proof. decode_bridge_ms. Qed.

(* add s7,s2,s4        # srcva := va0 + PGSIZE *)
Lemma csdb_01490bb3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01490bb3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 18), Regidx (mword_of_int 23), ADD), s).
Proof. decode_bridge_ms. Qed.

(* beq a1,a4,+0xa0     # max ran out -> return -1 *)
Lemma csdb_04e58463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x04e58463 : mword 32)) s
  = Some (BTYPE (mword_of_int 72 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 11), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* and s2,s7,s6        # va0 = PGROUNDDOWN(srcva)   <-- outer head *)
Lemma csdb_016bf933 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x016bf933 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 23), Regidx (mword_of_int 18), AND), s).
Proof. decode_bridge_ms. Qed.

(* jal ra,walkaddr     # -1336 -> 0x80000ff6 *)
Lemma csdb_ac9ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xac9ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095816 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* sub a3,s2,s7        # a3 := va0 - srcva *)
Lemma csdb_417906b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x417906b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 18), Regidx (mword_of_int 13), SUB), s).
Proof. decode_bridge_ms. Qed.

(* bgeu s3,a3,+0x78    # n = min(n, max) *)
Lemma csdb_00d9f363 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00d9f363 : mword 32)) s
  = Some (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 19), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* add a2,a0,s7 *)
Lemma csdb_01750633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x01750633 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 10), Regidx (mword_of_int 12), ADD), s).
Proof. decode_bridge_ms. Qed.

(* sub a2,a2,s2        # a2 := p = pa0 + (srcva - va0) *)
Lemma csdb_41260633 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x41260633 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 12), Regidx (mword_of_int 12), SUB), s).
Proof. decode_bridge_ms. Qed.

(* add a4,a2,a5        # a4 := the source byte's address *)
Lemma csdb_00f60733 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f60733 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD), s).
Proof. decode_bridge_ms. Qed.

(* lbu a4,0(a4) *)
Lemma csdb_00074703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00074703 : mword 32)) s
  = Some (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1), s).
Proof. decode_bridge_ms. Qed.

(* sb a4,0(a5)         # *dst = *p *)
Lemma csdb_00e78023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e78023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1), s).
Proof. decode_bridge_ms. Qed.

(* bne a5,a3,-0x12     # -> +0x88 *)
Lemma csdb_fed797e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfed797e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BNE), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section InstrsCS.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Lemma csi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x00) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 88 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)).  (* c.beqz a3,+0xb0    # max == 0 -> return -1, no frame *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x00)%Z (mword_of_int 0xcac5 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x00) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 88 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)) csdc_cac5 exec_execute_C_BEQZ. Qed.

  Lemma csi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x02) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,-80   # 80-byte frame: ra/s0/s1..s7 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x02)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x02) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  Lemma csi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,72(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x04)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  Lemma csi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,64(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x06)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  Lemma csi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* c.sdsp s1,56(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x08)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  Lemma csi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* c.sdsp s2,48(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x0a)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  Lemma csi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).  (* c.sdsp s3,40(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x0c)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  Lemma csi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).  (* c.sdsp s4,32(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x0e)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  Lemma csi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).  (* c.sdsp s5,24(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x10)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  Lemma csi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).  (* c.sdsp s6,16(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x12)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  Lemma csi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).  (* c.sdsp s7,8(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x14)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  Lemma csi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x16) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,80 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x16)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x16) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  Lemma csi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)).  (* c.mv s5,a0          # s5 := pagetable *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x18)%Z (mword_of_int 0x8aaa : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 21), ADD)) csdc_8aaa exec_execute_C_MV. Qed.

  Lemma csi_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,a1          # s1 := dst *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x1a)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma csi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 23), ADD)).  (* c.mv s7,a2          # s7 := srcva *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x1c)%Z (mword_of_int 0x8bb2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 23), ADD)) csdc_8bb2 exec_execute_C_MV. Qed.

  Lemma csi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 19), ADD)).  (* c.mv s3,a3          # s3 := max *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x1e)%Z (mword_of_int 0x89b6 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 19), ADD)) csdc_89b6 exec_execute_C_MV. Qed.

  Lemma csi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x20) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 22), LUI)).  (* c.lui s6,0xfffff    # s6 := -4096 (PGROUNDDOWN mask) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x20)%Z (mword_of_int 0x7b7d : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x20) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 22), LUI)) csdc_7b7d exec_execute_C_LUI. Qed.

  Lemma csi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x22) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), LUI)).  (* c.lui s4,0x1        # s4 := PGSIZE *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x22)%Z (mword_of_int 0x6a05 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x22) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 20), LUI)) csdc_6a05 exec_execute_C_LUI. Qed.

  Lemma csi_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x24) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")), zreg)).  (* c.j +0x5e           # enter the outer loop at its head *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x24)%Z (mword_of_int 0xa82d : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x24) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 29 : mword 11) ('b"0")), zreg)) csdc_a82d exec_execute_C_J. Qed.

  Lemma csi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x26) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)).  (* sb zero,0(a5)       # *dst = '\0' *)
  Proof. mk_base (KernelSyms.copyinstr + 0x26)%Z (mword_of_int 0x00078023 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x26) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 15), 1)) csdb_00078023. Qed.

  Lemma csi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).  (* c.li a5,1           # got_null = 1 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x2a)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma csi_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x2c) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), XORI)).  (* xori a5,a5,1        # a5 := !got_null *)
  Proof. mk_base (KernelSyms.copyinstr + 0x2c)%Z (mword_of_int 0x0017c793 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x2c) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), XORI)) csdb_0017c793. Qed.

  Lemma csi_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x30) : mword 64) false (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)).  (* negw a0,a5          # 0 -> 0, 1 -> -1 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x30)%Z (mword_of_int 0x40f0053b : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x30) : mword 64) (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)) csdb_40f0053b. Qed.

  Lemma csi_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x34) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,72(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x34)%Z (mword_of_int 0x60a6 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x34) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a6 exec_execute_C_LDSP. Qed.

  Lemma csi_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,64(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x36)%Z (mword_of_int 0x6406 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6406 exec_execute_C_LDSP. Qed.

  Lemma csi_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* c.ldsp s1,56(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x38)%Z (mword_of_int 0x74e2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74e2 exec_execute_C_LDSP. Qed.

  Lemma csi_3a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* c.ldsp s2,48(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x3a)%Z (mword_of_int 0x7942 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7942 exec_execute_C_LDSP. Qed.

  Lemma csi_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).  (* c.ldsp s3,40(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x3c)%Z (mword_of_int 0x79a2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79a2 exec_execute_C_LDSP. Qed.

  Lemma csi_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).  (* c.ldsp s4,32(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x3e)%Z (mword_of_int 0x7a02 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a02 exec_execute_C_LDSP. Qed.

  Lemma csi_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x40) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).  (* c.ldsp s5,24(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x40)%Z (mword_of_int 0x6ae2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6ae2 exec_execute_C_LDSP. Qed.

  Lemma csi_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).  (* c.ldsp s6,16(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x42)%Z (mword_of_int 0x6b42 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b42 exec_execute_C_LDSP. Qed.

  Lemma csi_44 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).  (* c.ldsp s7,8(sp) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x44)%Z (mword_of_int 0x6ba2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6ba2 exec_execute_C_LDSP. Qed.

  Lemma csi_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x46) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)).  (* c.addi16sp sp,80 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x46)%Z (mword_of_int 0x6161 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x46) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 5 : mword 6), sp, sp, ADDI)) cdec_6161 exec_execute_C_ADDI16SP. Qed.

  Lemma csi_48 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x48) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x48)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x48) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma csi_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x4a) : mword 64) false (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ADDI)).  (* addi a4,s3,-1       # a4 := rem - 1 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x4a)%Z (mword_of_int 0xfff98713 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x4a) : mword 64) (ITYPE (mword_of_int 4095 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 14), ADDI)) csdb_fff98713. Qed.

  Lemma csi_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x4e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).  (* c.add a4,a4,s1      # a4 := dst_base + (rem-1) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x4e)%Z (mword_of_int 0x9726 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x4e) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) csdc_9726 exec_execute_C_ADD. Qed.

  Lemma csi_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x50) : mword 64) false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 14), Regidx (mword_of_int 19), SUB)).  (* sub s3,a4,a1        # max -= n *)
  Proof. mk_base (KernelSyms.copyinstr + 0x50)%Z (mword_of_int 0x40b709b3 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 14), Regidx (mword_of_int 19), SUB)) csdb_40b709b3. Qed.

  Lemma csi_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x54) : mword 64) false (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 18), Regidx (mword_of_int 23), ADD)).  (* add s7,s2,s4        # srcva := va0 + PGSIZE *)
  Proof. mk_base (KernelSyms.copyinstr + 0x54)%Z (mword_of_int 0x01490bb3 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x54) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 18), Regidx (mword_of_int 23), ADD)) csdb_01490bb3. Qed.

  Lemma csi_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x58) : mword 64) false (BTYPE (mword_of_int 72 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 11), BEQ)).  (* beq a1,a4,+0xa0     # max ran out -> return -1 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x58)%Z (mword_of_int 0x04e58463 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x58) : mword 64) (BTYPE (mword_of_int 72 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 11), BEQ)) csdb_04e58463. Qed.

  Lemma csi_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,a5          # dst := dst_base + n *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x5c)%Z (mword_of_int 0x84be : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 9), ADD)) cdec_84be exec_execute_C_MV. Qed.

  Lemma csi_5e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x5e) : mword 64) false (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 23), Regidx (mword_of_int 18), AND)).  (* and s2,s7,s6        # va0 = PGROUNDDOWN(srcva)   <-- outer head *)
  Proof. mk_base (KernelSyms.copyinstr + 0x5e)%Z (mword_of_int 0x016bf933 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x5e) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 23), Regidx (mword_of_int 18), AND)) csdb_016bf933. Qed.

  Lemma csi_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x62) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s2 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x62)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x62) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma csi_64 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x64) : mword 64) true (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s5 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x64)%Z (mword_of_int 0x8556 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x64) : mword 64) (RTYPE (Regidx (mword_of_int 21), zreg, Regidx (mword_of_int 10), ADD)) csdc_8556 exec_execute_C_MV. Qed.

  Lemma csi_66 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x66) : mword 64) false (JAL (mword_of_int 2095816 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,walkaddr     # -1336 -> 0x80000ff6 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x66)%Z (mword_of_int 0xac9ff0ef : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x66) : mword 64) (JAL (mword_of_int 2095816 : mword 21, Regidx (mword_of_int 1))) csdb_ac9ff0ef. Qed.

  Lemma csi_6a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x6a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).  (* c.beqz a0,+0xa4     # unmapped -> return -1 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x6a)%Z (mword_of_int 0xcd0d : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x6a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) csdc_cd0d exec_execute_C_BEQZ. Qed.

  Lemma csi_6c : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x6c) : mword 64) false (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 18), Regidx (mword_of_int 13), SUB)).  (* sub a3,s2,s7        # a3 := va0 - srcva *)
  Proof. mk_base (KernelSyms.copyinstr + 0x6c)%Z (mword_of_int 0x417906b3 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x6c) : mword 64) (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 18), Regidx (mword_of_int 13), SUB)) csdb_417906b3. Qed.

  Lemma csi_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x70) : mword 64) true (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)).  (* c.add a3,a3,s4      # n := PGSIZE - (srcva - va0) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x70)%Z (mword_of_int 0x96d2 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x70) : mword 64) (RTYPE (Regidx (mword_of_int 20), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)) csdc_96d2 exec_execute_C_ADD. Qed.

  Lemma csi_72 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x72) : mword 64) false (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 19), BGEU)).  (* bgeu s3,a3,+0x78    # n = min(n, max) *)
  Proof. mk_base (KernelSyms.copyinstr + 0x72)%Z (mword_of_int 0x00d9f363 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x72) : mword 64) (BTYPE (mword_of_int 6 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 19), BGEU)) csdb_00d9f363. Qed.

  Lemma csi_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x76) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 13), ADD)).  (* c.mv a3,s3 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x76)%Z (mword_of_int 0x86ce : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x76) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 13), ADD)) csdc_86ce exec_execute_C_MV. Qed.

  Lemma csi_78 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x78) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 24 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)).  (* c.beqz a3,+0xa8     # DEAD: n >= 1 always *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x78)%Z (mword_of_int 0xca85 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x78) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 24 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 5)), BEQ)) csdc_ca85 exec_execute_C_BEQZ. Qed.

  Lemma csi_7a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x7a) : mword 64) false (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 10), Regidx (mword_of_int 12), ADD)).  (* add a2,a0,s7 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x7a)%Z (mword_of_int 0x01750633 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 23), Regidx (mword_of_int 10), Regidx (mword_of_int 12), ADD)) csdb_01750633. Qed.

  Lemma csi_7e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x7e) : mword 64) false (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 12), Regidx (mword_of_int 12), SUB)).  (* sub a2,a2,s2        # a2 := p = pa0 + (srcva - va0) *)
  Proof. mk_base (KernelSyms.copyinstr + 0x7e)%Z (mword_of_int 0x41260633 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x7e) : mword 64) (RTYPE (Regidx (mword_of_int 18), Regidx (mword_of_int 12), Regidx (mword_of_int 12), SUB)) csdb_41260633. Qed.

  Lemma csi_82 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x82) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 15), ADD)).  (* c.mv a5,s1          # a5 := dst cursor *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x82)%Z (mword_of_int 0x87a6 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x82) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 15), ADD)) csdc_87a6 exec_execute_C_MV. Qed.

  Lemma csi_84 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x84) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SUB)).  (* c.sub a2,a2,s1      # a2 := p - dst  (the source/dest delta) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x84)%Z (mword_of_int 0x8e05 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x84) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 4)), creg2reg_idx (Cregidx (mword_of_int 4)), SUB)) csdc_8e05 exec_execute_C_SUB. Qed.

  Lemma csi_86 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x86) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)).  (* c.add a3,a3,s1      # a3 := dst + n  (the end pointer) *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x86)%Z (mword_of_int 0x96a6 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x86) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 13), Regidx (mword_of_int 13), ADD)) csdc_96a6 exec_execute_C_ADD. Qed.

  Lemma csi_88 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x88) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,a5          # <-- inner head; a1 records the cursor *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x88)%Z (mword_of_int 0x85be : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x88) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 11), ADD)) csdc_85be exec_execute_C_MV. Qed.

  Lemma csi_8a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x8a) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)).  (* add a4,a2,a5        # a4 := the source byte's address *)
  Proof. mk_base (KernelSyms.copyinstr + 0x8a)%Z (mword_of_int 0x00f60733 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x8a) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)) csdb_00f60733. Qed.

  Lemma csi_8e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x8e) : mword 64) false (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1)).  (* lbu a4,0(a4) *)
  Proof. mk_base (KernelSyms.copyinstr + 0x8e)%Z (mword_of_int 0x00074703 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x8e) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), true, 1)) csdb_00074703. Qed.

  Lemma csi_92 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x92) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 202 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).  (* c.beqz a4,-0x6c     # -> +0x26, the NUL was found *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x92)%Z (mword_of_int 0xdb51 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x92) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 202 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) csdc_db51 exec_execute_C_BEQZ. Qed.

  Lemma csi_94 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x94) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)).  (* sb a4,0(a5)         # *dst = *p *)
  Proof. mk_base (KernelSyms.copyinstr + 0x94)%Z (mword_of_int 0x00e78023 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x94) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), 1)) csdb_00e78023. Qed.

  Lemma csi_98 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x98) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).  (* c.addi a5,a5,1 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x98)%Z (mword_of_int 0x0785 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x98) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) csdc_0785 exec_execute_C_ADDI. Qed.

  Lemma csi_9a : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x9a) : mword 64) false (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BNE)).  (* bne a5,a3,-0x12     # -> +0x88 *)
  Proof. mk_base (KernelSyms.copyinstr + 0x9a)%Z (mword_of_int 0xfed797e3 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0x9a) : mword 64) (BTYPE (mword_of_int 8174 : mword 13, Regidx (mword_of_int 13), Regidx (mword_of_int 15), BNE)) csdb_fed797e3. Qed.

  Lemma csi_9e : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0x9e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")), zreg)).  (* c.j -0x54           # -> +0x4a, the chunk is done *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0x9e)%Z (mword_of_int 0xb775 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0x9e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2006 : mword 11) ('b"0")), zreg)) csdc_b775 exec_execute_C_J. Qed.

  Lemma csi_a0 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xa0) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).  (* c.li a5,0           # got_null = 0 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xa0)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xa0) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  Lemma csi_a2 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xa2) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1989 : mword 11) ('b"0")), zreg)).  (* c.j -0x76           # -> +0x2c *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xa2)%Z (mword_of_int 0xb769 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xa2) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1989 : mword 11) ('b"0")), zreg)) csdc_b769 exec_execute_C_J. Qed.

  Lemma csi_a4 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xa4) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).  (* c.li a0,-1          # the walkaddr-failure return *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xa4)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xa4) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma csi_a6 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xa6) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)).  (* c.j -0x72           # -> +0x34, the epilogue *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xa6)%Z (mword_of_int 0xb779 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xa6) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)) csdc_b779 exec_execute_C_J. Qed.

  Lemma csi_b0 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xb0) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).  (* c.li a5,0           # max == 0: got_null = 0 *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xb0)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xb0) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  Lemma csi_b2 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xb2) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), XORI)).  (* xori a5,a5,1 *)
  Proof. mk_base (KernelSyms.copyinstr + 0xb2)%Z (mword_of_int 0x0017c793 : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0xb2) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), XORI)) csdb_0017c793. Qed.

  Lemma csi_b6 : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xb6) : mword 64) false (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)).  (* negw a0,a5          # -1 *)
  Proof. mk_base (KernelSyms.copyinstr + 0xb6)%Z (mword_of_int 0x40f0053b : mword 32)
    (mword_of_int (KernelSyms.copyinstr + 0xb6) : mword 64) (RTYPEW (Regidx (mword_of_int 15), Regidx (mword_of_int 0), Regidx (mword_of_int 10), SUBW)) csdb_40f0053b. Qed.

  Lemma csi_ba : kernel_text -∗ instr (mword_of_int (KernelSyms.copyinstr + 0xba) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret               # the frameless return *)
  Proof. mk_rvc (KernelSyms.copyinstr + 0xba)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.copyinstr + 0xba) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End InstrsCS.


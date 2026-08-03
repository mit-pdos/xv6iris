(* CodePiperead.v -- the instruction-DECODE layer for xv6's piperead().
   For EVERY instruction of

     piperead @ 0x80004596 .. 0x80004686   (offsets 0x00 .. 0xf0, 90 in all)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pri_<off>])
   plus the per-instruction decode facts they consume.  Same shape as
   CodePipeclose / CodePipealloc: [mk_rvc] for compressed
   instructions, [mk_base] for 4-byte ones.  Every compressed word the rest
   of the tree already decodes comes from KernelRvcDecode as [cdec_<word>];
   only the words nothing else uses are local ([prdc_<word>], and
   [prdb_<word>] for the 4-byte ones).

   piperead is SHRINK-WRAPPED the same way: ra/s0..s5 in the prologue,
   s6..s8 saved on each of the three paths that reach the copy loop
   (+0x56, +0x5e, +0x70) and reloaded at +0xd0 before the common epilogue;
   the killed/-1 exit at +0x66 never saved them.  The 1-byte local [ch]
   lives at s0-81.

   Body (all instruction bytes from the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/pipe.c):

     0x00 711d       addi sp,sp,-96
     0x02 ec86       sd ra,88(sp)
     0x04 e8a2       sd s0,80(sp)
     0x06 e4a6       sd s1,72(sp)
     0x08 e0ca       sd s2,64(sp)
     0x0a fc4e       sd s3,56(sp)
     0x0c f852       sd s4,48(sp)
     0x0e f456       sd s5,40(sp)
     0x10 1080       addi s0,sp,96
     0x12 84aa       mv s1,a0
     0x14 892e       mv s2,a1
     0x16 8ab2       mv s5,a2
     0x18 b56fd0ef   jal 80001904 <myproc>
     0x1c 8a2a       mv s4,a0
     0x1e 8526       mv a0,s1
     0x20 e52fc0ef   jal 80000c08 <acquire>
     0x24 2184a703   lw a4,536(s1)
     0x28 21c4a783   lw a5,540(s1)
     0x2c 21848993   addi s3,s1,536
     0x30 02f71763   bne a4,a5,800045f4 <piperead+0x5e>
     0x34 2244a783   lw a5,548(s1)
     0x38 cf85       beqz a5,80004606 <piperead+0x70>
     0x3a 8552       mv a0,s4
     0x3c b71fd0ef   jal 80002142 <killed>
     0x40 e11d       bnez a0,800045fc <piperead+0x66>
     0x42 85a6       mv a1,s1
     0x44 854e       mv a0,s3
     0x46 92bfd0ef   jal 80001f06 <sleep>
     0x4a 2184a703   lw a4,536(s1)
     0x4e 21c4a783   lw a5,540(s1)
     0x52 fef701e3   beq a4,a5,800045ca <piperead+0x34>
     0x56 f05a       sd s6,32(sp)
     0x58 ec5e       sd s7,24(sp)
     0x5a e862       sd s8,16(sp)
     0x5c a829       j 8000460c <piperead+0x76>
     0x5e f05a       sd s6,32(sp)
     0x60 ec5e       sd s7,24(sp)
     0x62 e862       sd s8,16(sp)
     0x64 a809       j 8000460c <piperead+0x76>
     0x66 8526       mv a0,s1
     0x68 e92fc0ef   jal 80000c90 <release>
     0x6c 59fd       li s3,-1
     0x6e a0a5       j 8000466c <piperead+0xd6>
     0x70 f05a       sd s6,32(sp)
     0x72 ec5e       sd s7,24(sp)
     0x74 e862       sd s8,16(sp)
     0x76 4981       li s3,0
     0x78 faf40c13   addi s8,s0,-81
     0x7c 4b85       li s7,1
     0x7e 5b7d       li s6,-1
     0x80 05505163   blez s5,80004658 <piperead+0xc2>
     0x84 2184a783   lw a5,536(s1)
     0x88 21c4a703   lw a4,540(s1)
     0x8c 02f70b63   beq a4,a5,80004658 <piperead+0xc2>
     0x90 1ff7f793   andi a5,a5,511
     0x94 97a6       add a5,a5,s1
     0x96 0187c783   lbu a5,24(a5)
     0x9a faf407a3   sb a5,-81(s0)
     0x9e 86de       mv a3,s7
     0xa0 8662       mv a2,s8
     0xa2 85ca       mv a1,s2
     0xa4 050a3503   ld a0,80(s4)
     0xa8 fe7fc0ef   jal 80001624 <copyout>
     0xac 03650f63   beq a0,s6,80004680 <piperead+0xea>
     0xb0 2184a783   lw a5,536(s1)
     0xb4 2785       addiw a5,a5,1
     0xb6 20f4ac23   sw a5,536(s1)
     0xba 2985       addiw s3,s3,1
     0xbc 0905       addi s2,s2,1
     0xbe fd3a93e3   bne s5,s3,8000461a <piperead+0x84>
     0xc2 21c48513   addi a0,s1,540
     0xc6 8f7fd0ef   jal 80001f52 <wakeup>
     0xca 8526       mv a0,s1
     0xcc e2efc0ef   jal 80000c90 <release>
     0xd0 7b02       ld s6,32(sp)
     0xd2 6be2       ld s7,24(sp)
     0xd4 6c42       ld s8,16(sp)
     0xd6 854e       mv a0,s3
     0xd8 60e6       ld ra,88(sp)
     0xda 6446       ld s0,80(sp)
     0xdc 64a6       ld s1,72(sp)
     0xde 6906       ld s2,64(sp)
     0xe0 79e2       ld s3,56(sp)
     0xe2 7a42       ld s4,48(sp)
     0xe4 7aa2       ld s5,40(sp)
     0xe6 6125       addi sp,sp,96
     0xe8 8082       ret
     0xea fc099ce3   bnez s3,80004658 <piperead+0xc2>
     0xee 89aa       mv s3,a0
     0xf0 bfc9       j 80004658 <piperead+0xc2>
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
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

Notation PR := KernelSyms.piperead.

(* ===================================================================== *)
(* Compressed decode facts for the words no other function uses.          *)
(* ===================================================================== *)



(* 0xe11d  bnez a0,800045fc <piperead+0x66> *)
Lemma prdc_e11d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe11d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 19, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0xa829  j 8000460c <piperead+0x76> *)
Lemma prdc_a829 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa829 : mword 16)) s
  = Some (C_J (mword_of_int 13), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x59fd  li s3,-1 *)
Lemma prdc_59fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x59fd : mword 16)) s
  = Some (C_LI (mword_of_int 63, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xa0a5  j 8000466c <piperead+0xd6> *)
Lemma prdc_a0a5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa0a5 : mword 16)) s
  = Some (C_J (mword_of_int 52), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* [cdec_4b85] (li s7,1) -- shared, see KernelRvcDecode.v *)




(* 0x8662  mv a2,s8 *)
Lemma prdc_8662 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8662 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 12), Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2985  addiw s3,s3,1 *)
Lemma prdc_2985 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x2985 : mword 16)) s
  = Some (C_ADDIW (mword_of_int 1, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x0905  addi s2,s2,1 *)
Lemma prdc_0905 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0905 : mword 16)) s
  = Some (C_ADDI (mword_of_int 1, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xbfc9  j 80004658 <piperead+0xc2> *)
(* [cdec_bfc9] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0xb56fd0ef  jal 80001904 <myproc> *)
Lemma prdb_b56fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb56fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2085718 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe52fc0ef  jal 80000c08 <acquire> *)
Lemma prdb_e52fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe52fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082386 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x2184a703  lw a4,536(s1) *)
Lemma prdb_2184a703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2184a703 : mword 32)) s
  = Some (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.


(* 0x21848993  addi s3,s1,536 *)
Lemma prdb_21848993 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x21848993 : mword 32)) s
  = Some (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x02f71763  bne a4,a5,800045f4 <piperead+0x5e> *)
Lemma prdb_02f71763 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f71763 : mword 32)) s
  = Some (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE), s).
Proof. decode_bridge_ms. Qed.


(* 0xb71fd0ef  jal 80002142 <killed> *)
Lemma prdb_b71fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb71fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087792 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x92bfd0ef  jal 80001f06 <sleep> *)
Lemma prdb_92bfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x92bfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087210 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfef701e3  beq a4,a5,800045ca <piperead+0x34> *)
Lemma prdb_fef701e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfef701e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0xe92fc0ef  jal 80000c90 <release> *)
Lemma prdb_e92fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe92fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082450 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfaf40c13  addi s8,s0,-81 *)
Lemma prdb_faf40c13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaf40c13 : mword 32)) s
  = Some (ITYPE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x05505163  blez s5,80004658 <piperead+0xc2> *)
Lemma prdb_05505163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x05505163 : mword 32)) s
  = Some (BTYPE (mword_of_int 66 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 0), BGE), s).
Proof. decode_bridge_ms. Qed.



(* 0x02f70b63  beq a4,a5,80004658 <piperead+0xc2> *)
Lemma prdb_02f70b63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02f70b63 : mword 32)) s
  = Some (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ), s).
Proof. decode_bridge_ms. Qed.



(* 0xfaf407a3  sb a5,-81(s0) *)
Lemma prdb_faf407a3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfaf407a3 : mword 32)) s
  = Some (STORE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 1), s).
Proof. decode_bridge_ms. Qed.

(* 0x050a3503  ld a0,80(s4) *)
Lemma prdb_050a3503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x050a3503 : mword 32)) s
  = Some (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* 0xfe7fc0ef  jal 80001624 <copyout> *)
Lemma prdb_fe7fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe7fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084838 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x03650f63  beq a0,s6,80004680 <piperead+0xea> *)
Lemma prdb_03650f63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03650f63 : mword 32)) s
  = Some (BTYPE (mword_of_int 62 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x20f4ac23  sw a5,536(s1) *)
Lemma prdb_20f4ac23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x20f4ac23 : mword 32)) s
  = Some (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4), s).
Proof. decode_bridge_ms. Qed.

(* 0xfd3a93e3  bne s5,s3,8000461a <piperead+0x84> *)
Lemma prdb_fd3a93e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd3a93e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8134 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 21), BNE), s).
Proof. decode_bridge_ms. Qed.


(* 0x8f7fd0ef  jal 80001f52 <wakeup> *)
Lemma prdb_8f7fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8f7fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087158 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xe2efc0ef  jal 80000c90 <release> *)
Lemma prdb_e2efc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe2efc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082350 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0xfc099ce3  bnez s3,80004658 <piperead+0xc2> *)
Lemma prdb_fc099ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc099ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8152 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 19), BNE), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section PipereadInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* +0x00  711d  addi sp,sp,-96 *)
  Lemma pri_00 : kernel_text -∗ instr (mword_of_int (PR + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PR + 0x00)%Z (mword_of_int 0x711d : mword 16)
    (mword_of_int (PR + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 58 : mword 6), sp, sp, ADDI)) cdec_711d exec_execute_C_ADDI16SP. Qed.

  (* +0x02  ec86  sd ra,88(sp) *)
  Lemma pri_02 : kernel_text -∗ instr (mword_of_int (PR + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PR + 0x02)%Z (mword_of_int 0xec86 : mword 16)
    (mword_of_int (PR + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec86 exec_execute_C_SDSP. Qed.

  (* +0x04  e8a2  sd s0,80(sp) *)
  Lemma pri_04 : kernel_text -∗ instr (mword_of_int (PR + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PR + 0x04)%Z (mword_of_int 0xe8a2 : mword 16)
    (mword_of_int (PR + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e8a2 exec_execute_C_SDSP. Qed.

  (* +0x06  e4a6  sd s1,72(sp) *)
  Lemma pri_06 : kernel_text -∗ instr (mword_of_int (PR + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PR + 0x06)%Z (mword_of_int 0xe4a6 : mword 16)
    (mword_of_int (PR + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e4a6 exec_execute_C_SDSP. Qed.

  (* +0x08  e0ca  sd s2,64(sp) *)
  Lemma pri_08 : kernel_text -∗ instr (mword_of_int (PR + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PR + 0x08)%Z (mword_of_int 0xe0ca : mword 16)
    (mword_of_int (PR + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e0ca exec_execute_C_SDSP. Qed.

  (* +0x0a  fc4e  sd s3,56(sp) *)
  Lemma pri_0a : kernel_text -∗ instr (mword_of_int (PR + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (PR + 0x0a)%Z (mword_of_int 0xfc4e : mword 16)
    (mword_of_int (PR + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_fc4e exec_execute_C_SDSP. Qed.

  (* +0x0c  f852  sd s4,48(sp) *)
  Lemma pri_0c : kernel_text -∗ instr (mword_of_int (PR + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (PR + 0x0c)%Z (mword_of_int 0xf852 : mword 16)
    (mword_of_int (PR + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f852 exec_execute_C_SDSP. Qed.

  (* +0x0e  f456  sd s5,40(sp) *)
  Lemma pri_0e : kernel_text -∗ instr (mword_of_int (PR + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (PR + 0x0e)%Z (mword_of_int 0xf456 : mword 16)
    (mword_of_int (PR + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_f456 exec_execute_C_SDSP. Qed.

  (* +0x10  1080  addi s0,sp,96 *)
  Lemma pri_10 : kernel_text -∗ instr (mword_of_int (PR + 0x10) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PR + 0x10)%Z (mword_of_int 0x1080 : mword 16)
    (mword_of_int (PR + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 24 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1080 exec_execute_C_ADDI4SPN. Qed.

  (* +0x12  84aa  mv s1,a0 *)
  Lemma pri_12 : kernel_text -∗ instr (mword_of_int (PR + 0x12) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PR + 0x12)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (PR + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  (* +0x14  892e  mv s2,a1 *)
  Lemma pri_14 : kernel_text -∗ instr (mword_of_int (PR + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PR + 0x14)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (PR + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  (* +0x16  8ab2  mv s5,a2 *)
  Lemma pri_16 : kernel_text -∗ instr (mword_of_int (PR + 0x16) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (PR + 0x16)%Z (mword_of_int 0x8ab2 : mword 16)
    (mword_of_int (PR + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 21), ADD)) cdec_8ab2 exec_execute_C_MV. Qed.

  (* +0x18  b56fd0ef  jal 80001904 <myproc> *)
  Lemma pri_18 : kernel_text -∗ instr (mword_of_int (PR + 0x18) : mword 64) false (JAL (mword_of_int 2085718 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0x18)%Z (mword_of_int 0xb56fd0ef : mword 32)
    (mword_of_int (PR + 0x18) : mword 64) (JAL (mword_of_int 2085718 : mword 21, Regidx (mword_of_int 1))) prdb_b56fd0ef. Qed.

  (* +0x1c  8a2a  mv s4,a0 *)
  Lemma pri_1c : kernel_text -∗ instr (mword_of_int (PR + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (PR + 0x1c)%Z (mword_of_int 0x8a2a : mword 16)
    (mword_of_int (PR + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.

  (* +0x1e  8526  mv a0,s1 *)
  Lemma pri_1e : kernel_text -∗ instr (mword_of_int (PR + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0x1e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PR + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0x20  e52fc0ef  jal 80000c08 <acquire> *)
  Lemma pri_20 : kernel_text -∗ instr (mword_of_int (PR + 0x20) : mword 64) false (JAL (mword_of_int 2082386 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0x20)%Z (mword_of_int 0xe52fc0ef : mword 32)
    (mword_of_int (PR + 0x20) : mword 64) (JAL (mword_of_int 2082386 : mword 21, Regidx (mword_of_int 1))) prdb_e52fc0ef. Qed.

  (* +0x24  2184a703  lw a4,536(s1) *)
  Lemma pri_24 : kernel_text -∗ instr (mword_of_int (PR + 0x24) : mword 64) false (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (PR + 0x24)%Z (mword_of_int 0x2184a703 : mword 32)
    (mword_of_int (PR + 0x24) : mword 64) (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) prdb_2184a703. Qed.

  (* +0x28  21c4a783  lw a5,540(s1) *)
  Lemma pri_28 : kernel_text -∗ instr (mword_of_int (PR + 0x28) : mword 64) false (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PR + 0x28)%Z (mword_of_int 0x21c4a783 : mword 32)
    (mword_of_int (PR + 0x28) : mword 64) (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_21c4a783. Qed.

  (* +0x2c  21848993  addi s3,s1,536 *)
  Lemma pri_2c : kernel_text -∗ instr (mword_of_int (PR + 0x2c) : mword 64) false (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), ADDI)).
  Proof. mk_base (PR + 0x2c)%Z (mword_of_int 0x21848993 : mword 32)
    (mword_of_int (PR + 0x2c) : mword 64) (ITYPE (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 19), ADDI)) prdb_21848993. Qed.

  (* +0x30  02f71763  bne a4,a5,800045f4 <piperead+0x5e> *)
  Lemma pri_30 : kernel_text -∗ instr (mword_of_int (PR + 0x30) : mword 64) false (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)).
  Proof. mk_base (PR + 0x30)%Z (mword_of_int 0x02f71763 : mword 32)
    (mword_of_int (PR + 0x30) : mword 64) (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BNE)) prdb_02f71763. Qed.

  (* +0x34  2244a783  lw a5,548(s1) *)
  Lemma pri_34 : kernel_text -∗ instr (mword_of_int (PR + 0x34) : mword 64) false (LOAD (mword_of_int 548 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PR + 0x34)%Z (mword_of_int 0x2244a783 : mword 32)
    (mword_of_int (PR + 0x34) : mword 64) (LOAD (mword_of_int 548 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2244a783. Qed.

  (* +0x38  cf85  beqz a5,80004606 <piperead+0x70> *)
  Lemma pri_38 : kernel_text -∗ instr (mword_of_int (PR + 0x38) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PR + 0x38)%Z (mword_of_int 0xcf85 : mword 16)
    (mword_of_int (PR + 0x38) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 28 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_cf85 exec_execute_C_BEQZ. Qed.

  (* +0x3a  8552  mv a0,s4 *)
  Lemma pri_3a : kernel_text -∗ instr (mword_of_int (PR + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0x3a)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (PR + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  (* +0x3c  b71fd0ef  jal 80002142 <killed> *)
  Lemma pri_3c : kernel_text -∗ instr (mword_of_int (PR + 0x3c) : mword 64) false (JAL (mword_of_int 2087792 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0x3c)%Z (mword_of_int 0xb71fd0ef : mword 32)
    (mword_of_int (PR + 0x3c) : mword 64) (JAL (mword_of_int 2087792 : mword 21, Regidx (mword_of_int 1))) prdb_b71fd0ef. Qed.

  (* +0x40  e11d  bnez a0,800045fc <piperead+0x66> *)
  Lemma pri_40 : kernel_text -∗ instr (mword_of_int (PR + 0x40) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (PR + 0x40)%Z (mword_of_int 0xe11d : mword 16)
    (mword_of_int (PR + 0x40) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 19 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) prdc_e11d exec_execute_C_BNEZ. Qed.

  (* +0x42  85a6  mv a1,s1 *)
  Lemma pri_42 : kernel_text -∗ instr (mword_of_int (PR + 0x42) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PR + 0x42)%Z (mword_of_int 0x85a6 : mword 16)
    (mword_of_int (PR + 0x42) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 11), ADD)) cdec_85a6 exec_execute_C_MV. Qed.

  (* +0x44  854e  mv a0,s3 *)
  Lemma pri_44 : kernel_text -∗ instr (mword_of_int (PR + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0x44)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (PR + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  (* +0x46  92bfd0ef  jal 80001f06 <sleep> *)
  Lemma pri_46 : kernel_text -∗ instr (mword_of_int (PR + 0x46) : mword 64) false (JAL (mword_of_int 2087210 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0x46)%Z (mword_of_int 0x92bfd0ef : mword 32)
    (mword_of_int (PR + 0x46) : mword 64) (JAL (mword_of_int 2087210 : mword 21, Regidx (mword_of_int 1))) prdb_92bfd0ef. Qed.

  (* +0x4a  2184a703  lw a4,536(s1) *)
  Lemma pri_4a : kernel_text -∗ instr (mword_of_int (PR + 0x4a) : mword 64) false (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (PR + 0x4a)%Z (mword_of_int 0x2184a703 : mword 32)
    (mword_of_int (PR + 0x4a) : mword 64) (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) prdb_2184a703. Qed.

  (* +0x4e  21c4a783  lw a5,540(s1) *)
  Lemma pri_4e : kernel_text -∗ instr (mword_of_int (PR + 0x4e) : mword 64) false (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PR + 0x4e)%Z (mword_of_int 0x21c4a783 : mword 32)
    (mword_of_int (PR + 0x4e) : mword 64) (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_21c4a783. Qed.

  (* +0x52  fef701e3  beq a4,a5,800045ca <piperead+0x34> *)
  Lemma pri_52 : kernel_text -∗ instr (mword_of_int (PR + 0x52) : mword 64) false (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (PR + 0x52)%Z (mword_of_int 0xfef701e3 : mword 32)
    (mword_of_int (PR + 0x52) : mword 64) (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) prdb_fef701e3. Qed.

  (* +0x56  f05a  sd s6,32(sp) *)
  Lemma pri_56 : kernel_text -∗ instr (mword_of_int (PR + 0x56) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PR + 0x56)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (PR + 0x56) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  (* +0x58  ec5e  sd s7,24(sp) *)
  Lemma pri_58 : kernel_text -∗ instr (mword_of_int (PR + 0x58) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (PR + 0x58)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (PR + 0x58) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  (* +0x5a  e862  sd s8,16(sp) *)
  Lemma pri_5a : kernel_text -∗ instr (mword_of_int (PR + 0x5a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (PR + 0x5a)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (PR + 0x5a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  (* +0x5c  a829  j 8000460c <piperead+0x76> *)
  Lemma pri_5c : kernel_text -∗ instr (mword_of_int (PR + 0x5c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PR + 0x5c)%Z (mword_of_int 0xa829 : mword 16)
    (mword_of_int (PR + 0x5c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 13 : mword 11) ('b"0")), zreg)) prdc_a829 exec_execute_C_J. Qed.

  (* +0x5e  f05a  sd s6,32(sp) *)
  Lemma pri_5e : kernel_text -∗ instr (mword_of_int (PR + 0x5e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PR + 0x5e)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (PR + 0x5e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  (* +0x60  ec5e  sd s7,24(sp) *)
  Lemma pri_60 : kernel_text -∗ instr (mword_of_int (PR + 0x60) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (PR + 0x60)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (PR + 0x60) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  (* +0x62  e862  sd s8,16(sp) *)
  Lemma pri_62 : kernel_text -∗ instr (mword_of_int (PR + 0x62) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (PR + 0x62)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (PR + 0x62) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  (* +0x64  a809  j 8000460c <piperead+0x76> *)
  Lemma pri_64 : kernel_text -∗ instr (mword_of_int (PR + 0x64) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PR + 0x64)%Z (mword_of_int 0xa809 : mword 16)
    (mword_of_int (PR + 0x64) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")), zreg)) cdec_a809 exec_execute_C_J. Qed.

  (* +0x66  8526  mv a0,s1 *)
  Lemma pri_66 : kernel_text -∗ instr (mword_of_int (PR + 0x66) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0x66)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PR + 0x66) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0x68  e92fc0ef  jal 80000c90 <release> *)
  Lemma pri_68 : kernel_text -∗ instr (mword_of_int (PR + 0x68) : mword 64) false (JAL (mword_of_int 2082450 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0x68)%Z (mword_of_int 0xe92fc0ef : mword 32)
    (mword_of_int (PR + 0x68) : mword 64) (JAL (mword_of_int 2082450 : mword 21, Regidx (mword_of_int 1))) prdb_e92fc0ef. Qed.

  (* +0x6c  59fd  li s3,-1 *)
  Lemma pri_6c : kernel_text -∗ instr (mword_of_int (PR + 0x6c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (PR + 0x6c)%Z (mword_of_int 0x59fd : mword 16)
    (mword_of_int (PR + 0x6c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) prdc_59fd exec_execute_C_LI. Qed.

  (* +0x6e  a0a5  j 8000466c <piperead+0xd6> *)
  Lemma pri_6e : kernel_text -∗ instr (mword_of_int (PR + 0x6e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 52 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PR + 0x6e)%Z (mword_of_int 0xa0a5 : mword 16)
    (mword_of_int (PR + 0x6e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 52 : mword 11) ('b"0")), zreg)) prdc_a0a5 exec_execute_C_J. Qed.

  (* +0x70  f05a  sd s6,32(sp) *)
  Lemma pri_70 : kernel_text -∗ instr (mword_of_int (PR + 0x70) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (PR + 0x70)%Z (mword_of_int 0xf05a : mword 16)
    (mword_of_int (PR + 0x70) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_f05a exec_execute_C_SDSP. Qed.

  (* +0x72  ec5e  sd s7,24(sp) *)
  Lemma pri_72 : kernel_text -∗ instr (mword_of_int (PR + 0x72) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (PR + 0x72)%Z (mword_of_int 0xec5e : mword 16)
    (mword_of_int (PR + 0x72) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_ec5e exec_execute_C_SDSP. Qed.

  (* +0x74  e862  sd s8,16(sp) *)
  Lemma pri_74 : kernel_text -∗ instr (mword_of_int (PR + 0x74) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (PR + 0x74)%Z (mword_of_int 0xe862 : mword 16)
    (mword_of_int (PR + 0x74) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e862 exec_execute_C_SDSP. Qed.

  (* +0x76  4981  li s3,0 *)
  Lemma pri_76 : kernel_text -∗ instr (mword_of_int (PR + 0x76) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (PR + 0x76)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (PR + 0x76) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  (* +0x78  faf40c13  addi s8,s0,-81 *)
  Lemma pri_78 : kernel_text -∗ instr (mword_of_int (PR + 0x78) : mword 64) false (ITYPE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI)).
  Proof. mk_base (PR + 0x78)%Z (mword_of_int 0xfaf40c13 : mword 32)
    (mword_of_int (PR + 0x78) : mword 64) (ITYPE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 24), ADDI)) prdb_faf40c13. Qed.

  (* +0x7c  4b85  li s7,1 *)
  Lemma pri_7c : kernel_text -∗ instr (mword_of_int (PR + 0x7c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)).
  Proof. mk_rvc (PR + 0x7c)%Z (mword_of_int 0x4b85 : mword 16)
    (mword_of_int (PR + 0x7c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)) cdec_4b85 exec_execute_C_LI. Qed.

  (* +0x7e  5b7d  li s6,-1 *)
  Lemma pri_7e : kernel_text -∗ instr (mword_of_int (PR + 0x7e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)).
  Proof. mk_rvc (PR + 0x7e)%Z (mword_of_int 0x5b7d : mword 16)
    (mword_of_int (PR + 0x7e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 22), ADDI)) cdec_5b7d exec_execute_C_LI. Qed.

  (* +0x80  05505163  blez s5,80004658 <piperead+0xc2> *)
  Lemma pri_80 : kernel_text -∗ instr (mword_of_int (PR + 0x80) : mword 64) false (BTYPE (mword_of_int 66 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 0), BGE)).
  Proof. mk_base (PR + 0x80)%Z (mword_of_int 0x05505163 : mword 32)
    (mword_of_int (PR + 0x80) : mword 64) (BTYPE (mword_of_int 66 : mword 13, Regidx (mword_of_int 21), Regidx (mword_of_int 0), BGE)) prdb_05505163. Qed.

  (* +0x84  2184a783  lw a5,536(s1) *)
  Lemma pri_84 : kernel_text -∗ instr (mword_of_int (PR + 0x84) : mword 64) false (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PR + 0x84)%Z (mword_of_int 0x2184a783 : mword 32)
    (mword_of_int (PR + 0x84) : mword 64) (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2184a783. Qed.

  (* +0x88  21c4a703  lw a4,540(s1) *)
  Lemma pri_88 : kernel_text -∗ instr (mword_of_int (PR + 0x88) : mword 64) false (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (PR + 0x88)%Z (mword_of_int 0x21c4a703 : mword 32)
    (mword_of_int (PR + 0x88) : mword 64) (LOAD (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 14), false, 4)) bdec_21c4a703. Qed.

  (* +0x8c  02f70b63  beq a4,a5,80004658 <piperead+0xc2> *)
  Lemma pri_8c : kernel_text -∗ instr (mword_of_int (PR + 0x8c) : mword 64) false (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)).
  Proof. mk_base (PR + 0x8c)%Z (mword_of_int 0x02f70b63 : mword 32)
    (mword_of_int (PR + 0x8c) : mword 64) (BTYPE (mword_of_int 54 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BEQ)) prdb_02f70b63. Qed.

  (* +0x90  1ff7f793  andi a5,a5,511 *)
  Lemma pri_90 : kernel_text -∗ instr (mword_of_int (PR + 0x90) : mword 64) false (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)).
  Proof. mk_base (PR + 0x90)%Z (mword_of_int 0x1ff7f793 : mword 32)
    (mword_of_int (PR + 0x90) : mword 64) (ITYPE (mword_of_int 511 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ANDI)) bdec_1ff7f793. Qed.

  (* +0x94  97a6  add a5,a5,s1 *)
  Lemma pri_94 : kernel_text -∗ instr (mword_of_int (PR + 0x94) : mword 64) true (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (PR + 0x94)%Z (mword_of_int 0x97a6 : mword 16)
    (mword_of_int (PR + 0x94) : mword 64) (RTYPE (Regidx (mword_of_int 9), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97a6 exec_execute_C_ADD. Qed.

  (* +0x96  0187c783  lbu a5,24(a5) *)
  Lemma pri_96 : kernel_text -∗ instr (mword_of_int (PR + 0x96) : mword 64) false (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)).
  Proof. mk_base (PR + 0x96)%Z (mword_of_int 0x0187c783 : mword 32)
    (mword_of_int (PR + 0x96) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), true, 1)) bdec_0187c783. Qed.

  (* +0x9a  faf407a3  sb a5,-81(s0) *)
  Lemma pri_9a : kernel_text -∗ instr (mword_of_int (PR + 0x9a) : mword 64) false (STORE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 1)).
  Proof. mk_base (PR + 0x9a)%Z (mword_of_int 0xfaf407a3 : mword 32)
    (mword_of_int (PR + 0x9a) : mword 64) (STORE (mword_of_int 4015 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 8), 1)) prdb_faf407a3. Qed.

  (* +0x9e  86de  mv a3,s7 *)
  Lemma pri_9e : kernel_text -∗ instr (mword_of_int (PR + 0x9e) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (PR + 0x9e)%Z (mword_of_int 0x86de : mword 16)
    (mword_of_int (PR + 0x9e) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 13), ADD)) cdec_86de exec_execute_C_MV. Qed.

  (* +0xa0  8662  mv a2,s8 *)
  Lemma pri_a0 : kernel_text -∗ instr (mword_of_int (PR + 0xa0) : mword 64) true (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 12), ADD)).
  Proof. mk_rvc (PR + 0xa0)%Z (mword_of_int 0x8662 : mword 16)
    (mword_of_int (PR + 0xa0) : mword 64) (RTYPE (Regidx (mword_of_int 24), zreg, Regidx (mword_of_int 12), ADD)) prdc_8662 exec_execute_C_MV. Qed.

  (* +0xa2  85ca  mv a1,s2 *)
  Lemma pri_a2 : kernel_text -∗ instr (mword_of_int (PR + 0xa2) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (PR + 0xa2)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (PR + 0xa2) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  (* +0xa4  050a3503  ld a0,80(s4) *)
  Lemma pri_a4 : kernel_text -∗ instr (mword_of_int (PR + 0xa4) : mword 64) false (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (PR + 0xa4)%Z (mword_of_int 0x050a3503 : mword 32)
    (mword_of_int (PR + 0xa4) : mword 64) (LOAD (mword_of_int 80 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 10), false, 8)) prdb_050a3503. Qed.

  (* +0xa8  fe7fc0ef  jal 80001624 <copyout> *)
  Lemma pri_a8 : kernel_text -∗ instr (mword_of_int (PR + 0xa8) : mword 64) false (JAL (mword_of_int 2084838 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0xa8)%Z (mword_of_int 0xfe7fc0ef : mword 32)
    (mword_of_int (PR + 0xa8) : mword 64) (JAL (mword_of_int 2084838 : mword 21, Regidx (mword_of_int 1))) prdb_fe7fc0ef. Qed.

  (* +0xac  03650f63  beq a0,s6,80004680 <piperead+0xea> *)
  Lemma pri_ac : kernel_text -∗ instr (mword_of_int (PR + 0xac) : mword 64) false (BTYPE (mword_of_int 62 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (PR + 0xac)%Z (mword_of_int 0x03650f63 : mword 32)
    (mword_of_int (PR + 0xac) : mword 64) (BTYPE (mword_of_int 62 : mword 13, Regidx (mword_of_int 22), Regidx (mword_of_int 10), BEQ)) prdb_03650f63. Qed.

  (* +0xb0  2184a783  lw a5,536(s1) *)
  Lemma pri_b0 : kernel_text -∗ instr (mword_of_int (PR + 0xb0) : mword 64) false (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PR + 0xb0)%Z (mword_of_int 0x2184a783 : mword 32)
    (mword_of_int (PR + 0xb0) : mword 64) (LOAD (mword_of_int 536 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2184a783. Qed.

  (* +0xb4  2785  addiw a5,a5,1 *)
  Lemma pri_b4 : kernel_text -∗ instr (mword_of_int (PR + 0xb4) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (PR + 0xb4)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (PR + 0xb4) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  (* +0xb6  20f4ac23  sw a5,536(s1) *)
  Lemma pri_b6 : kernel_text -∗ instr (mword_of_int (PR + 0xb6) : mword 64) false (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (PR + 0xb6)%Z (mword_of_int 0x20f4ac23 : mword 32)
    (mword_of_int (PR + 0xb6) : mword 64) (STORE (mword_of_int 536 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) prdb_20f4ac23. Qed.

  (* +0xba  2985  addiw s3,s3,1 *)
  Lemma pri_ba : kernel_text -∗ instr (mword_of_int (PR + 0xba) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19))).
  Proof. mk_rvc (PR + 0xba)%Z (mword_of_int 0x2985 : mword 16)
    (mword_of_int (PR + 0xba) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 19), Regidx (mword_of_int 19))) prdc_2985 exec_execute_C_ADDIW. Qed.

  (* +0xbc  0905  addi s2,s2,1 *)
  Lemma pri_bc : kernel_text -∗ instr (mword_of_int (PR + 0xbc) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_rvc (PR + 0xbc)%Z (mword_of_int 0x0905 : mword 16)
    (mword_of_int (PR + 0xbc) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) prdc_0905 exec_execute_C_ADDI. Qed.

  (* +0xbe  fd3a93e3  bne s5,s3,8000461a <piperead+0x84> *)
  Lemma pri_be : kernel_text -∗ instr (mword_of_int (PR + 0xbe) : mword 64) false (BTYPE (mword_of_int 8134 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 21), BNE)).
  Proof. mk_base (PR + 0xbe)%Z (mword_of_int 0xfd3a93e3 : mword 32)
    (mword_of_int (PR + 0xbe) : mword 64) (BTYPE (mword_of_int 8134 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 21), BNE)) prdb_fd3a93e3. Qed.

  (* +0xc2  21c48513  addi a0,s1,540 *)
  Lemma pri_c2 : kernel_text -∗ instr (mword_of_int (PR + 0xc2) : mword 64) false (ITYPE (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PR + 0xc2)%Z (mword_of_int 0x21c48513 : mword 32)
    (mword_of_int (PR + 0xc2) : mword 64) (ITYPE (mword_of_int 540 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_21c48513. Qed.

  (* +0xc6  8f7fd0ef  jal 80001f52 <wakeup> *)
  Lemma pri_c6 : kernel_text -∗ instr (mword_of_int (PR + 0xc6) : mword 64) false (JAL (mword_of_int 2087158 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0xc6)%Z (mword_of_int 0x8f7fd0ef : mword 32)
    (mword_of_int (PR + 0xc6) : mword 64) (JAL (mword_of_int 2087158 : mword 21, Regidx (mword_of_int 1))) prdb_8f7fd0ef. Qed.

  (* +0xca  8526  mv a0,s1 *)
  Lemma pri_ca : kernel_text -∗ instr (mword_of_int (PR + 0xca) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0xca)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PR + 0xca) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  (* +0xcc  e2efc0ef  jal 80000c90 <release> *)
  Lemma pri_cc : kernel_text -∗ instr (mword_of_int (PR + 0xcc) : mword 64) false (JAL (mword_of_int 2082350 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PR + 0xcc)%Z (mword_of_int 0xe2efc0ef : mword 32)
    (mword_of_int (PR + 0xcc) : mword 64) (JAL (mword_of_int 2082350 : mword 21, Regidx (mword_of_int 1))) prdb_e2efc0ef. Qed.

  (* +0xd0  7b02  ld s6,32(sp) *)
  Lemma pri_d0 : kernel_text -∗ instr (mword_of_int (PR + 0xd0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (PR + 0xd0)%Z (mword_of_int 0x7b02 : mword 16)
    (mword_of_int (PR + 0xd0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_7b02 exec_execute_C_LDSP. Qed.

  (* +0xd2  6be2  ld s7,24(sp) *)
  Lemma pri_d2 : kernel_text -∗ instr (mword_of_int (PR + 0xd2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)).
  Proof. mk_rvc (PR + 0xd2)%Z (mword_of_int 0x6be2 : mword 16)
    (mword_of_int (PR + 0xd2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 23), false, 8)) cdec_6be2 exec_execute_C_LDSP. Qed.

  (* +0xd4  6c42  ld s8,16(sp) *)
  Lemma pri_d4 : kernel_text -∗ instr (mword_of_int (PR + 0xd4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)).
  Proof. mk_rvc (PR + 0xd4)%Z (mword_of_int 0x6c42 : mword 16)
    (mword_of_int (PR + 0xd4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 24), false, 8)) cdec_6c42 exec_execute_C_LDSP. Qed.

  (* +0xd6  854e  mv a0,s3 *)
  Lemma pri_d6 : kernel_text -∗ instr (mword_of_int (PR + 0xd6) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PR + 0xd6)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (PR + 0xd6) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  (* +0xd8  60e6  ld ra,88(sp) *)
  Lemma pri_d8 : kernel_text -∗ instr (mword_of_int (PR + 0xd8) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PR + 0xd8)%Z (mword_of_int 0x60e6 : mword 16)
    (mword_of_int (PR + 0xd8) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 11 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e6 exec_execute_C_LDSP. Qed.

  (* +0xda  6446  ld s0,80(sp) *)
  Lemma pri_da : kernel_text -∗ instr (mword_of_int (PR + 0xda) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PR + 0xda)%Z (mword_of_int 0x6446 : mword 16)
    (mword_of_int (PR + 0xda) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6446 exec_execute_C_LDSP. Qed.

  (* +0xdc  64a6  ld s1,72(sp) *)
  Lemma pri_dc : kernel_text -∗ instr (mword_of_int (PR + 0xdc) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PR + 0xdc)%Z (mword_of_int 0x64a6 : mword 16)
    (mword_of_int (PR + 0xdc) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a6 exec_execute_C_LDSP. Qed.

  (* +0xde  6906  ld s2,64(sp) *)
  Lemma pri_de : kernel_text -∗ instr (mword_of_int (PR + 0xde) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PR + 0xde)%Z (mword_of_int 0x6906 : mword 16)
    (mword_of_int (PR + 0xde) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6906 exec_execute_C_LDSP. Qed.

  (* +0xe0  79e2  ld s3,56(sp) *)
  Lemma pri_e0 : kernel_text -∗ instr (mword_of_int (PR + 0xe0) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (PR + 0xe0)%Z (mword_of_int 0x79e2 : mword 16)
    (mword_of_int (PR + 0xe0) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_79e2 exec_execute_C_LDSP. Qed.

  (* +0xe2  7a42  ld s4,48(sp) *)
  Lemma pri_e2 : kernel_text -∗ instr (mword_of_int (PR + 0xe2) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (PR + 0xe2)%Z (mword_of_int 0x7a42 : mword 16)
    (mword_of_int (PR + 0xe2) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_7a42 exec_execute_C_LDSP. Qed.

  (* +0xe4  7aa2  ld s5,40(sp) *)
  Lemma pri_e4 : kernel_text -∗ instr (mword_of_int (PR + 0xe4) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (PR + 0xe4)%Z (mword_of_int 0x7aa2 : mword 16)
    (mword_of_int (PR + 0xe4) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_7aa2 exec_execute_C_LDSP. Qed.

  (* +0xe6  6125  addi sp,sp,96 *)
  Lemma pri_e6 : kernel_text -∗ instr (mword_of_int (PR + 0xe6) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PR + 0xe6)%Z (mword_of_int 0x6125 : mword 16)
    (mword_of_int (PR + 0xe6) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 6 : mword 6), sp, sp, ADDI)) cdec_6125 exec_execute_C_ADDI16SP. Qed.

  (* +0xe8  8082  ret *)
  Lemma pri_e8 : kernel_text -∗ instr (mword_of_int (PR + 0xe8) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PR + 0xe8)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PR + 0xe8) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* +0xea  fc099ce3  bnez s3,80004658 <piperead+0xc2> *)
  Lemma pri_ea : kernel_text -∗ instr (mword_of_int (PR + 0xea) : mword 64) false (BTYPE (mword_of_int 8152 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 19), BNE)).
  Proof. mk_base (PR + 0xea)%Z (mword_of_int 0xfc099ce3 : mword 32)
    (mword_of_int (PR + 0xea) : mword 64) (BTYPE (mword_of_int 8152 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 19), BNE)) prdb_fc099ce3. Qed.

  (* +0xee  89aa  mv s3,a0 *)
  Lemma pri_ee : kernel_text -∗ instr (mword_of_int (PR + 0xee) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (PR + 0xee)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (PR + 0xee) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  (* +0xf0  bfc9  j 80004658 <piperead+0xc2> *)
  Lemma pri_f0 : kernel_text -∗ instr (mword_of_int (PR + 0xf0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PR + 0xf0)%Z (mword_of_int 0xbfc9 : mword 16)
    (mword_of_int (PR + 0xf0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)) cdec_bfc9 exec_execute_C_J. Qed.

End PipereadInstrs.

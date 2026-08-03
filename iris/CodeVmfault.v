(* CodeVmfault.v -- the instruction-DECODE layer for xv6's vmfault().

     vmfault @ 0x800015a0 .. 0x80001623   (offsets 0x00 .. 0x82, 58 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([vfi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the eight 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; vmfault's own words are local, named [vfdc_<word>]
   (compressed) / [vfdb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/vm.c's lazy-allocation fault handler):

     0x00 7179       c.addi16sp sp,-48      # 48-byte frame; ra/s0/s2/s3 always
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 e84a       c.sdsp s2,16(sp)
     0x08 e44e       c.sdsp s3,8(sp)
     0x0a 1800       c.addi4spn s0,sp,48
     0x0c 89aa       c.mv   s3,a0           # s3 := pagetable
     0x0e 892e       c.mv   s2,a1           # s2 := va
     0x10 354000ef   jal    ra,myproc       # +852
     0x14 653c       c.ld   a5,72(a0)       # a5 := p->sz
     0x16 00f96a63   bltu   s2,a5,+0x14     # -> 0x2a, va < p->sz: the real work
     0x1a 4981       c.li   s3,0            # the 0 return
     0x1c 854e       c.mv   a0,s3           # <- ALL FOUR paths join here
     0x1e 70a2       c.ldsp ra,40(sp)
     0x20 7402       c.ldsp s0,32(sp)
     0x22 6942       c.ldsp s2,16(sp)
     0x24 69a2       c.ldsp s3,8(sp)
     0x26 6145       c.addi16sp sp,48
     0x28 8082       c.ret
     0x2a ec26       c.sdsp s1,24(sp)       # s1/s4 saved only past the sz test
     0x2c e052       c.sdsp s4,0(sp)
     0x2e 84aa       c.mv   s1,a0           # s1 := p
     0x30 77fd       c.lui  a5,0xfffff      # -4096
     0x32 00f97a33   and    s4,s2,a5        # s4 := PGROUNDDOWN(va)
     0x36 85d2       c.mv   a1,s4
     0x38 854e       c.mv   a0,s3
     0x3a fabff0ef   jal    ra,ismapped     # -86
     0x3e 4981       c.li   s3,0
     0x40 c501       c.beqz a0,+0x8         # -> 0x48, not mapped: allocate
     0x42 64e2       c.ldsp s1,24(sp)       # mapped -> return 0
     0x44 6a02       c.ldsp s4,0(sp)
     0x46 bfd9       c.j    -0x2a           # -> 0x1c
     0x48 d46ff0ef   jal    ra,kalloc       # -2746
     0x4c 892a       c.mv   s2,a0           # s2 := mem
     0x4e c905       c.beqz a0,+0x30        # -> 0x7e, out of memory
     0x50 89aa       c.mv   s3,a0           # s3 := mem (the success return)
     0x52 6605       c.lui  a2,0x1          # PGSIZE
     0x54 4581       c.li   a1,0
     0x56 ed2ff0ef   jal    ra,memset       # -2350
     0x5a 4759       c.li   a4,22           # PTE_R|PTE_W|PTE_U
     0x5c 86ca       c.mv   a3,s2
     0x5e 6605       c.lui  a2,0x1
     0x60 85d2       c.mv   a1,s4
     0x62 68a8       c.ld   a0,80(s1)       # p->pagetable
     0x64 a2dff0ef   jal    ra,mappages     # -1492
     0x68 e501       c.bnez a0,+0x8         # -> 0x70, mappages failed
     0x6a 64e2       c.ldsp s1,24(sp)       # success -> return mem
     0x6c 6a02       c.ldsp s4,0(sp)
     0x6e b77d       c.j    -0x52           # -> 0x1c
     0x70 854a       c.mv   a0,s2
     0x72 c34ff0ef   jal    ra,kfree        # -3020
     0x76 4981       c.li   s3,0
     0x78 64e2       c.ldsp s1,24(sp)
     0x7a 6a02       c.ldsp s4,0(sp)
     0x7c b745       c.j    -0x60           # -> 0x1c
     0x7e 64e2       c.ldsp s1,24(sp)       # kalloc-null -> return 0
     0x80 6a02       c.ldsp s4,0(sp)
     0x82 bf69       c.j    -0x66           # -> 0x1c

   Note the shrink-wrapped epilogue: the [va >= p->sz] arm falls straight into
   the join at 0x1c WITHOUT touching s1/s4, while each of the three long paths
   restores s1/s4 first and then jumps there -- so the epilogue at 0x1c..0x28
   is proved once and fed by four arms (the pipeclose join-structure recipe).

   All branch/jump immediates below are the DECODER's positive residues: the
   backward [c.j]s are 2027 / 2007 / 2000 / 1997 (2^11 complements of -21 /
   -41 / -48 / -51 half-words) and the backward [jal]s are 2097066 / 2094406 /
   2094802 / 2095660 / 2094132 (2^21 complements of the byte offsets).       *)
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
(* Compressed decode facts for vmfault's own words.                       *)
(* ===================================================================== *)

(* 0x0c / 0x50  c.mv s3,a0 -- [cdec_89aa] (KernelRvcDecode.v) *)

(* 0x14  c.ld a5,72(a0) -- [cdec_653c] (KernelRvcDecode.v; fetchaddr's too) *)



(* 0x30  c.lui a5,0xfffff  (imm6 = 63, the 6-bit residue of -1) *)
(* [cdec_77fd] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* [cdec_85d2] -- shared, see KernelRvcDecode.v *)

(* 0x40  c.beqz a0,+0x8 *)
Lemma vfdc_c501 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc501 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 4, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x4c  c.mv s2,a0 *)

(* 0x4e  c.beqz a0,+0x30 *)
Lemma vfdc_c905 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc905 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 24, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x5a  c.li a4,22 *)
Lemma vfdc_4759 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4759 : mword 16)) s
  = Some (C_LI (mword_of_int 22, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_86ca] -- shared, see KernelRvcDecode.v *)


(* 0x68  c.bnez a0,+0x8 *)
Lemma vfdc_e501 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe501 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 4, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x7c  c.j -0x60  (offset/2 = -48; 11-bit residue 2000) *)
Lemma vfdc_b745 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb745 : mword 16)) s
  = Some (C_J (mword_of_int 2000), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x82  c.j -0x66  (offset/2 = -51; 11-bit residue 1997) *)
Lemma vfdc_bf69 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf69 : mword 16)) s
  = Some (C_J (mword_of_int 1997), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all eight are vmfault's own.             *)
(* ===================================================================== *)

(* 0x10  jal ra,myproc     (0x800015b0 -> 0x80001904 is +852) *)
Lemma vfdb_354000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x354000ef : mword 32)) s
  = Some (JAL (mword_of_int 852 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x16  bltu s2,a5,+0x14  -- the [va < p->sz] test *)
Lemma vfdb_00f96a63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f96a63 : mword 32)) s
  = Some (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  and s4,s2,a5  -- PGROUNDDOWN(va) *)
Lemma vfdb_00f97a33 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f97a33 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 20), AND), s).
Proof. decode_bridge_ms. Qed.

(* 0x3a  jal ra,ismapped   (0x800015da -> 0x80001584 is -86) *)
Lemma vfdb_fabff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfabff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2097066 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x48  jal ra,kalloc     (0x800015e8 -> 0x80000b2e is -2746) *)
Lemma vfdb_d46ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd46ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094406 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x56  jal ra,memset     (0x800015f6 -> 0x80000cc8 is -2350) *)
Lemma vfdb_ed2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xed2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094802 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x64  jal ra,mappages   (0x80001604 -> 0x80001030 is -1492) *)
Lemma vfdb_a2dff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa2dff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095660 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x72  jal ra,kfree      (0x80001612 -> 0x80000a46 is -3020) *)
Lemma vfdb_c34ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc34ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094132 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section VmfaultInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation VF := KernelSyms.vmfault.

  (* --- prologue ------------------------------------------------------- *)

  Lemma vfi_00 : kernel_text -∗ instr (mword_of_int (VF + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VF + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (VF + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma vfi_02 : kernel_text -∗ instr (mword_of_int (VF + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (VF + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (VF + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma vfi_04 : kernel_text -∗ instr (mword_of_int (VF + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (VF + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (VF + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma vfi_06 : kernel_text -∗ instr (mword_of_int (VF + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (VF + 0x06)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (VF + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma vfi_08 : kernel_text -∗ instr (mword_of_int (VF + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (VF + 0x08)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (VF + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma vfi_0a : kernel_text -∗ instr (mword_of_int (VF + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (VF + 0x0a)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (VF + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma vfi_0c : kernel_text -∗ instr (mword_of_int (VF + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (VF + 0x0c)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (VF + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma vfi_0e : kernel_text -∗ instr (mword_of_int (VF + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (VF + 0x0e)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (VF + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  (* --- myproc(), the p->sz test, and the short 0-return -------------- *)

  Lemma vfi_10 : kernel_text -∗ instr (mword_of_int (VF + 0x10) : mword 64) false (JAL (mword_of_int 852 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x10)%Z (mword_of_int 0x354000ef : mword 32)
    (mword_of_int (VF + 0x10) : mword 64) (JAL (mword_of_int 852 : mword 21, Regidx (mword_of_int 1))) vfdb_354000ef. Qed.

  Lemma vfi_14 : kernel_text -∗ instr (mword_of_int (VF + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (VF + 0x14)%Z (mword_of_int 0x653c : mword 16)
    (mword_of_int (VF + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) cdec_653c exec_execute_C_LD. Qed.

  Lemma vfi_16 : kernel_text -∗ instr (mword_of_int (VF + 0x16) : mword 64) false (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLTU)).
  Proof. mk_base (VF + 0x16)%Z (mword_of_int 0x00f96a63 : mword 32)
    (mword_of_int (VF + 0x16) : mword 64) (BTYPE (mword_of_int 20 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 18), BLTU)) vfdb_00f96a63. Qed.

  Lemma vfi_1a : kernel_text -∗ instr (mword_of_int (VF + 0x1a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (VF + 0x1a)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (VF + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  (* --- the common epilogue, joined by all four exit paths ------------- *)

  Lemma vfi_1c : kernel_text -∗ instr (mword_of_int (VF + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (VF + 0x1c)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (VF + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  Lemma vfi_1e : kernel_text -∗ instr (mword_of_int (VF + 0x1e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (VF + 0x1e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (VF + 0x1e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma vfi_20 : kernel_text -∗ instr (mword_of_int (VF + 0x20) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (VF + 0x20)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (VF + 0x20) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma vfi_22 : kernel_text -∗ instr (mword_of_int (VF + 0x22) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (VF + 0x22)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (VF + 0x22) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma vfi_24 : kernel_text -∗ instr (mword_of_int (VF + 0x24) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (VF + 0x24)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (VF + 0x24) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma vfi_26 : kernel_text -∗ instr (mword_of_int (VF + 0x26) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (VF + 0x26)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (VF + 0x26) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma vfi_28 : kernel_text -∗ instr (mword_of_int (VF + 0x28) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (VF + 0x28)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (VF + 0x28) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- past the sz test: save s1/s4, PGROUNDDOWN, ismapped() --------- *)

  Lemma vfi_2a : kernel_text -∗ instr (mword_of_int (VF + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (VF + 0x2a)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (VF + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma vfi_2c : kernel_text -∗ instr (mword_of_int (VF + 0x2c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (VF + 0x2c)%Z (mword_of_int 0xe052 : mword 16)
    (mword_of_int (VF + 0x2c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e052 exec_execute_C_SDSP. Qed.

  Lemma vfi_2e : kernel_text -∗ instr (mword_of_int (VF + 0x2e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (VF + 0x2e)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (VF + 0x2e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma vfi_30 : kernel_text -∗ instr (mword_of_int (VF + 0x30) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (VF + 0x30)%Z (mword_of_int 0x77fd : mword 16)
    (mword_of_int (VF + 0x30) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), LUI)) cdec_77fd exec_execute_C_LUI. Qed.

  Lemma vfi_32 : kernel_text -∗ instr (mword_of_int (VF + 0x32) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 20), AND)).
  Proof. mk_base (VF + 0x32)%Z (mword_of_int 0x00f97a33 : mword 32)
    (mword_of_int (VF + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 18), Regidx (mword_of_int 20), AND)) vfdb_00f97a33. Qed.

  Lemma vfi_36 : kernel_text -∗ instr (mword_of_int (VF + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (VF + 0x36)%Z (mword_of_int 0x85d2 : mword 16)
    (mword_of_int (VF + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)) cdec_85d2 exec_execute_C_MV. Qed.

  Lemma vfi_38 : kernel_text -∗ instr (mword_of_int (VF + 0x38) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (VF + 0x38)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (VF + 0x38) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) cdec_854e exec_execute_C_MV. Qed.

  Lemma vfi_3a : kernel_text -∗ instr (mword_of_int (VF + 0x3a) : mword 64) false (JAL (mword_of_int 2097066 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x3a)%Z (mword_of_int 0xfabff0ef : mword 32)
    (mword_of_int (VF + 0x3a) : mword 64) (JAL (mword_of_int 2097066 : mword 21, Regidx (mword_of_int 1))) vfdb_fabff0ef. Qed.

  Lemma vfi_3e : kernel_text -∗ instr (mword_of_int (VF + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (VF + 0x3e)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (VF + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  Lemma vfi_40 : kernel_text -∗ instr (mword_of_int (VF + 0x40) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (VF + 0x40)%Z (mword_of_int 0xc501 : mword 16)
    (mword_of_int (VF + 0x40) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) vfdc_c501 exec_execute_C_BEQZ. Qed.

  (* --- already mapped: restore s1/s4 and rejoin ---------------------- *)

  Lemma vfi_42 : kernel_text -∗ instr (mword_of_int (VF + 0x42) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VF + 0x42)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (VF + 0x42) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma vfi_44 : kernel_text -∗ instr (mword_of_int (VF + 0x44) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (VF + 0x44)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (VF + 0x44) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma vfi_46 : kernel_text -∗ instr (mword_of_int (VF + 0x46) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VF + 0x46)%Z (mword_of_int 0xbfd9 : mword 16)
    (mword_of_int (VF + 0x46) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)) cdec_bfd9 exec_execute_C_J. Qed.

  (* --- kalloc / memset / mappages ------------------------------------ *)

  Lemma vfi_48 : kernel_text -∗ instr (mword_of_int (VF + 0x48) : mword 64) false (JAL (mword_of_int 2094406 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x48)%Z (mword_of_int 0xd46ff0ef : mword 32)
    (mword_of_int (VF + 0x48) : mword 64) (JAL (mword_of_int 2094406 : mword 21, Regidx (mword_of_int 1))) vfdb_d46ff0ef. Qed.

  Lemma vfi_4c : kernel_text -∗ instr (mword_of_int (VF + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (VF + 0x4c)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (VF + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma vfi_4e : kernel_text -∗ instr (mword_of_int (VF + 0x4e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 24 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (VF + 0x4e)%Z (mword_of_int 0xc905 : mword 16)
    (mword_of_int (VF + 0x4e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 24 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) vfdc_c905 exec_execute_C_BEQZ. Qed.

  Lemma vfi_50 : kernel_text -∗ instr (mword_of_int (VF + 0x50) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (VF + 0x50)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (VF + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma vfi_52 : kernel_text -∗ instr (mword_of_int (VF + 0x52) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (VF + 0x52)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (VF + 0x52) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.

  Lemma vfi_54 : kernel_text -∗ instr (mword_of_int (VF + 0x54) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (VF + 0x54)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (VF + 0x54) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma vfi_56 : kernel_text -∗ instr (mword_of_int (VF + 0x56) : mword 64) false (JAL (mword_of_int 2094802 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x56)%Z (mword_of_int 0xed2ff0ef : mword 32)
    (mword_of_int (VF + 0x56) : mword 64) (JAL (mword_of_int 2094802 : mword 21, Regidx (mword_of_int 1))) vfdb_ed2ff0ef. Qed.

  Lemma vfi_5a : kernel_text -∗ instr (mword_of_int (VF + 0x5a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 22 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)).
  Proof. mk_rvc (VF + 0x5a)%Z (mword_of_int 0x4759 : mword 16)
    (mword_of_int (VF + 0x5a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 22 : mword 6), zreg, Regidx (mword_of_int 14), ADDI)) vfdc_4759 exec_execute_C_LI. Qed.

  Lemma vfi_5c : kernel_text -∗ instr (mword_of_int (VF + 0x5c) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)).
  Proof. mk_rvc (VF + 0x5c)%Z (mword_of_int 0x86ca : mword 16)
    (mword_of_int (VF + 0x5c) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 13), ADD)) cdec_86ca exec_execute_C_MV. Qed.

  Lemma vfi_5e : kernel_text -∗ instr (mword_of_int (VF + 0x5e) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)).
  Proof. mk_rvc (VF + 0x5e)%Z (mword_of_int 0x6605 : mword 16)
    (mword_of_int (VF + 0x5e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 12), LUI)) cdec_6605 exec_execute_C_LUI. Qed.

  Lemma vfi_60 : kernel_text -∗ instr (mword_of_int (VF + 0x60) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (VF + 0x60)%Z (mword_of_int 0x85d2 : mword 16)
    (mword_of_int (VF + 0x60) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 11), ADD)) cdec_85d2 exec_execute_C_MV. Qed.

  Lemma vfi_62 : kernel_text -∗ instr (mword_of_int (VF + 0x62) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)).
  Proof. mk_rvc (VF + 0x62)%Z (mword_of_int 0x68a8 : mword 16)
    (mword_of_int (VF + 0x62) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 10 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 2)), false, 8)) cdec_68a8 exec_execute_C_LD. Qed.

  Lemma vfi_64 : kernel_text -∗ instr (mword_of_int (VF + 0x64) : mword 64) false (JAL (mword_of_int 2095660 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x64)%Z (mword_of_int 0xa2dff0ef : mword 32)
    (mword_of_int (VF + 0x64) : mword 64) (JAL (mword_of_int 2095660 : mword 21, Regidx (mword_of_int 1))) vfdb_a2dff0ef. Qed.

  Lemma vfi_68 : kernel_text -∗ instr (mword_of_int (VF + 0x68) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (VF + 0x68)%Z (mword_of_int 0xe501 : mword 16)
    (mword_of_int (VF + 0x68) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) vfdc_e501 exec_execute_C_BNEZ. Qed.

  (* --- mappages succeeded: return mem -------------------------------- *)

  Lemma vfi_6a : kernel_text -∗ instr (mword_of_int (VF + 0x6a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VF + 0x6a)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (VF + 0x6a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma vfi_6c : kernel_text -∗ instr (mword_of_int (VF + 0x6c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (VF + 0x6c)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (VF + 0x6c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma vfi_6e : kernel_text -∗ instr (mword_of_int (VF + 0x6e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VF + 0x6e)%Z (mword_of_int 0xb77d : mword 16)
    (mword_of_int (VF + 0x6e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2007 : mword 11) ('b"0")), zreg)) cdec_b77d exec_execute_C_J. Qed.

  (* --- mappages failed: kfree the page and return 0 ------------------ *)

  Lemma vfi_70 : kernel_text -∗ instr (mword_of_int (VF + 0x70) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (VF + 0x70)%Z (mword_of_int 0x854a : mword 16)
    (mword_of_int (VF + 0x70) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 10), ADD)) cdec_854a exec_execute_C_MV. Qed.

  Lemma vfi_72 : kernel_text -∗ instr (mword_of_int (VF + 0x72) : mword 64) false (JAL (mword_of_int 2094132 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (VF + 0x72)%Z (mword_of_int 0xc34ff0ef : mword 32)
    (mword_of_int (VF + 0x72) : mword 64) (JAL (mword_of_int 2094132 : mword 21, Regidx (mword_of_int 1))) vfdb_c34ff0ef. Qed.

  Lemma vfi_76 : kernel_text -∗ instr (mword_of_int (VF + 0x76) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (VF + 0x76)%Z (mword_of_int 0x4981 : mword 16)
    (mword_of_int (VF + 0x76) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) cdec_4981 exec_execute_C_LI. Qed.

  Lemma vfi_78 : kernel_text -∗ instr (mword_of_int (VF + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VF + 0x78)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (VF + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma vfi_7a : kernel_text -∗ instr (mword_of_int (VF + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (VF + 0x7a)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (VF + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma vfi_7c : kernel_text -∗ instr (mword_of_int (VF + 0x7c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2000 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VF + 0x7c)%Z (mword_of_int 0xb745 : mword 16)
    (mword_of_int (VF + 0x7c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2000 : mword 11) ('b"0")), zreg)) vfdc_b745 exec_execute_C_J. Qed.

  (* --- kalloc returned 0: return 0 ----------------------------------- *)

  Lemma vfi_7e : kernel_text -∗ instr (mword_of_int (VF + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (VF + 0x7e)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (VF + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma vfi_80 : kernel_text -∗ instr (mword_of_int (VF + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (VF + 0x80)%Z (mword_of_int 0x6a02 : mword 16)
    (mword_of_int (VF + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a02 exec_execute_C_LDSP. Qed.

  Lemma vfi_82 : kernel_text -∗ instr (mword_of_int (VF + 0x82) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (VF + 0x82)%Z (mword_of_int 0xbf69 : mword 16)
    (mword_of_int (VF + 0x82) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1997 : mword 11) ('b"0")), zreg)) vfdc_bf69 exec_execute_C_J. Qed.

End VmfaultInstrs.

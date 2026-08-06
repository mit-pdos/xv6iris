(* CodeAllocproc.v -- the instruction-DECODE layer for xv6's allocproc().
   For every instruction of

     allocproc @ 0x80001b28 .. 0x80001bac   (offsets 0x00 .. 0x84)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([api_<off>]).

   THE TWO FAILURE TAILS ARE NOT HERE.  Offsets 0x86 .. 0xa4 are the
   [freeproc(p); release(&p->lock); return 0] arms after a failed kalloc /
   proc_pagetable.  allocproc's contract is counted-only, so both [c.beqz]
   tests FALL THROUGH and neither tail is ever decoded -- exactly the way
   proc_pagetable's own uvmfree/uvmunmap tails are dead.  Adding them would
   be decoding code the proof can never reach.

     0x00 1101       c.addi     sp,sp,-32
     0x02 ec06       c.sdsp     ra,24(sp)
     0x04 e822       c.sdsp     s0,16(sp)
     0x06 e426       c.sdsp     s1,8(sp)
     0x08 e04a       c.sdsp     s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32
     0x0c 00011497   auipc      s1,0x11          # s1 := &proc[0]
     0x10 c4448493   addi       s1,s1,-956
     0x14 00016917   auipc      s2,0x16          # s2 := &proc[NPROC] = <tickslock>
     0x18 63c90913   addi       s2,s2,1596
     0x1c 8526       c.mv       a0,s1        <-- LOOP HEAD
     0x1e 8c2ff0ef   jal        ra,acquire
     0x22 4c9c       c.lw       a5,24(s1)        # p->state
     0x24 cb91       c.beqz     a5,+0x14         # -> +0x38  (UNUSED: found)
     0x26 8526       c.mv       a0,s1
     0x28 940ff0ef   jal        ra,release
     0x2c 16848493   addi       s1,s1,360        # p++
     0x30 ff2496e3   bne        s1,s2,-0x14      # -> +0x1c
     0x34 4481       c.li       s1,0             # table full: return 0
     0x36 a089       c.j        +0x42            # -> +0x78
     0x38 e71ff0ef   jal        ra,allocpid  <-- found
     0x3c d888       c.sw       a0,48(s1)        # p->pid
     0x3e 4785       c.li       a5,1
     0x40 cc9c       c.sw       a5,24(s1)        # p->state = USED
     0x42 fc5fe0ef   jal        ra,kalloc
     0x46 892a       c.mv       s2,a0
     0x48 eca8       c.sd       a0,88(s1)        # p->trapframe
     0x4a cd15       c.beqz     a0,+0x3c         # -> +0x86  (DEAD)
     0x4c 8526       c.mv       a0,s1
     0x4e e99ff0ef   jal        ra,proc_pagetable
     0x52 892a       c.mv       s2,a0
     0x54 e8a8       c.sd       a0,80(s1)        # p->pagetable
     0x56 c121       c.beqz     a0,+0x40         # -> +0x96  (DEAD)
     0x58 07000613   addi       a2,zero,112      # sizeof(struct context)
     0x5c 4581       c.li       a1,0
     0x5e 06048513   addi       a0,s1,96         # &p->context
     0x62 93eff0ef   jal        ra,memset
     0x66 00000797   auipc      a5,0x0           # a5 := forkret
     0x6a da878793   addi       a5,a5,-600
     0x6e f0bc       c.sd       a5,96(s1)        # p->context.ra
     0x70 60bc       c.ld       a5,64(s1)        # p->kstack
     0x72 6705       c.lui      a4,0x1           # PGSIZE
     0x74 97ba       c.add      a5,a5,a4
     0x76 f4bc       c.sd       a5,104(s1)       # p->context.sp
     0x78 8526       c.mv       a0,s1        <-- BOTH exits join here
     0x7a 60e2       c.ldsp     ra,24(sp)
     0x7c 6442       c.ldsp     s0,16(sp)
     0x7e 64a2       c.ldsp     s1,8(sp)
     0x80 6902       c.ldsp     s2,0(sp)
     0x82 6105       c.addi16sp sp,32
     0x84 8082       c.ret

   The 32-byte four-register frame is kalloc's, so its eleven words come from
   KernelRvcDecode's shared base, as do [c.mv a0,s1], [c.li a5,1],
   [c.li a1,0], [c.sw a5,24(s1)] (the p->state store sleep and yield share)
   and [c.add a5,a5,a4]. *)
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
(* Compressed words allocproc does not share with another decode file.    *)
(* ===================================================================== *)

(* +0x22  c.lw a5,24(s1) -- p->state -- is the shared KernelRvcDecode.cdec_4c9c *)


(* +0x36  c.j +0x42 *)
Lemma apdc_a089 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa089 : mword 16)) s
  = Some (C_J (mword_of_int 33), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x3c  c.sw a0,48(s1)  -- p->pid *)
Lemma apdc_d888 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd888 : mword 16)) s
  = Some (C_SW (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* +0x48  c.sd a0,88(s1)  -- p->trapframe *)
Lemma apdc_eca8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xeca8 : mword 16)) s
  = Some (C_SD (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x4a  c.beqz a0,+0x3c *)
Lemma apdc_cd15 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcd15 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 30, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x54  c.sd a0,80(s1)  -- p->pagetable *)
Lemma apdc_e8a8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe8a8 : mword 16)) s
  = Some (C_SD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* +0x6e  c.sd a5,96(s1)  -- p->context.ra *)
Lemma apdc_f0bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf0bc : mword 16)) s
  = Some (C_SD (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x70  c.ld a5,64(s1)  -- p->kstack *)
Lemma apdc_60bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x60bc : mword 16)) s
  = Some (C_LD (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x72  c.lui a4,0x1  -- PGSIZE *)
Lemma apdc_6705 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6705 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x76  c.sd a5,104(s1)  -- p->context.sp *)
Lemma apdc_f4bc s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf4bc : mword 16)) s
  = Some (C_SD (mword_of_int 13, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ---- their leaf-form expansions: the shape a WP memory leaf takes, with a
   literal [mword 12] displacement and plain [Regidx]es. ---- *)

(* the lw24 s1->a5 shape is the shared KernelRvcDecode.cexec_lw24_s1_a5 *)

Lemma apexec_sw48_s1_a0 s :
  exec (execute (C_SW (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 48, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 4)), s).
Proof. apply exec_execute_C_SW_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apexec_sd88_s1_a0 s :
  exec (execute (C_SD (mword_of_int 11, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 88, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apexec_sd80_s1_a0 s :
  exec (execute (C_SD (mword_of_int 10, Cregidx (mword_of_int 1), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (STORE (mword_of_int 80, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apexec_sd96_s1_a5 s :
  exec (execute (C_SD (mword_of_int 12, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 96, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apexec_sd104_s1_a5 s :
  exec (execute (C_SD (mword_of_int 13, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 104, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma apexec_ld64_s1_a5 s :
  exec (execute (C_LD (mword_of_int 8, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)


(* +0x10  addi s1,s1,-956  (the 12-bit field is 2^12 - 956 = 3140) *)
Lemma apdb_c4448493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc4448493 : mword 32)) s
  = Some (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.


(* +0x18  addi s2,s2,1596 *)
Lemma apdb_63c90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x63c90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 1596 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  jal ra,acquire   (0x80001b46 -> 0x80000c08 is -3902; 2^21 - 3902) *)
Lemma apdb_8c2ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8c2ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093250 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x28  jal ra,release   (0x80001b50 -> 0x80000c90 is -3776) *)
Lemma apdb_940ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x940ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093376 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


(* +0x30  bne s1,s2,-0x14  (the 13-bit field is 2^13 - 20 = 8172) *)
Lemma apdb_ff2496e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff2496e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* +0x38  jal ra,allocpid  (0x80001b60 -> 0x800019d0 is -400) *)
Lemma apdb_e71ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe71ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096752 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x42  jal ra,kalloc  (0x80001b6a -> 0x80000b2e is -4156) *)
Lemma apdb_fc5fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc5fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092996 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x4e  jal ra,proc_pagetable  (0x80001b76 -> 0x80001a0e is -360) *)
Lemma apdb_e99ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe99ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096792 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x58  li a2,112 *)
Lemma apdb_07000613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x07000613 : mword 32)) s
  = Some (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.


(* +0x62  jal ra,memset  (0x80001b8a -> 0x80000cc8 is -3778) *)
Lemma apdb_93eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x93eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093374 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x66  auipc a5,0x0 *)
Lemma apdb_00000797 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00000797 : mword 32)) s
  = Some (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 15), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x6a  addi a5,a5,-600  (the 12-bit field is 2^12 - 600 = 3496) *)
Lemma apdb_da878793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xda878793 : mword 32)) s
  = Some (ITYPE (mword_of_int 3496 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section AllocprocInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma api_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma api_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma api_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma api_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma api_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma api_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma api_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KernelSyms.allocproc + 0x0c)%Z (mword_of_int 0x00011497 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x0c) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_00011497. Qed.

  Lemma api_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x10) : mword 64) false (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x10)%Z (mword_of_int 0xc4448493 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x10) : mword 64) (ITYPE (mword_of_int 3140 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) apdb_c4448493. Qed.

  Lemma api_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x14) : mword 64) false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KernelSyms.allocproc + 0x14)%Z (mword_of_int 0x00016917 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x14) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)) bdec_00016917. Qed.

  Lemma api_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x18) : mword 64) false (ITYPE (mword_of_int 1596 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x18)%Z (mword_of_int 0x63c90913 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x18) : mword 64) (ITYPE (mword_of_int 1596 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) apdb_63c90913. Qed.

  Lemma api_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x1c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma api_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) false (JAL (mword_of_int 2093250 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x1e)%Z (mword_of_int 0x8c2ff0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x1e) : mword 64) (JAL (mword_of_int 2093250 : mword 21, Regidx (mword_of_int 1))) apdb_8c2ff0ef. Qed.

  Lemma api_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x22) : mword 64) true (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x22)%Z (mword_of_int 0x4c9c : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x22) : mword 64) (LOAD (mword_of_int 24 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_4c9c cexec_lw24_s1_a5. Qed.

  Lemma api_24 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x24) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x24)%Z (mword_of_int 0xcb91 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x24) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 10 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_cb91 exec_execute_C_BEQZ. Qed.

  Lemma api_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x26)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma api_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) false (JAL (mword_of_int 2093376 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x28)%Z (mword_of_int 0x940ff0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x28) : mword 64) (JAL (mword_of_int 2093376 : mword 21, Regidx (mword_of_int 1))) apdb_940ff0ef. Qed.

  Lemma api_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x2c) : mword 64) false (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x2c)%Z (mword_of_int 0x16848493 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x2c) : mword 64) (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bdec_16848493. Qed.

  Lemma api_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x30) : mword 64) false (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (KernelSyms.allocproc + 0x30)%Z (mword_of_int 0xff2496e3 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x30) : mword 64) (BTYPE (mword_of_int 8172 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BNE)) apdb_ff2496e3. Qed.

  Lemma api_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x34) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x34)%Z (mword_of_int 0x4481 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x34) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) cdec_4481 exec_execute_C_LI. Qed.

  Lemma api_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x36) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 33 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x36)%Z (mword_of_int 0xa089 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x36) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 33 : mword 11) ('b"0")), zreg)) apdc_a089 exec_execute_C_J. Qed.

  Lemma api_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) false (JAL (mword_of_int 2096752 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x38)%Z (mword_of_int 0xe71ff0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x38) : mword 64) (JAL (mword_of_int 2096752 : mword 21, Regidx (mword_of_int 1))) apdb_e71ff0ef. Qed.

  Lemma api_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x3c) : mword 64) true (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x3c)%Z (mword_of_int 0xd888 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x3c) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 4)) apdc_d888 apexec_sw48_s1_a0. Qed.

  Lemma api_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x3e)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma api_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) true (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x40)%Z (mword_of_int 0xcc9c : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x40) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_cc9c cexec_cc9c. Qed.

  Lemma api_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x42) : mword 64) false (JAL (mword_of_int 2092996 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x42)%Z (mword_of_int 0xfc5fe0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x42) : mword 64) (JAL (mword_of_int 2092996 : mword 21, Regidx (mword_of_int 1))) apdb_fc5fe0ef. Qed.

  Lemma api_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x46) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x46)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x46) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma api_48 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x48) : mword 64) true (STORE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x48)%Z (mword_of_int 0xeca8 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x48) : mword 64) (STORE (mword_of_int 88 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) apdc_eca8 apexec_sd88_s1_a0. Qed.

  Lemma api_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x4a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x4a)%Z (mword_of_int 0xcd15 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x4a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 30 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) apdc_cd15 exec_execute_C_BEQZ. Qed.

  Lemma api_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x4c) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x4c)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x4c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma api_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x4e) : mword 64) false (JAL (mword_of_int 2096792 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x4e)%Z (mword_of_int 0xe99ff0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x4e) : mword 64) (JAL (mword_of_int 2096792 : mword 21, Regidx (mword_of_int 1))) apdb_e99ff0ef. Qed.

  Lemma api_52 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x52)%Z (mword_of_int 0x892a : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x52) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 18), ADD)) cdec_892a exec_execute_C_MV. Qed.

  Lemma api_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x54) : mword 64) true (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x54)%Z (mword_of_int 0xe8a8 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x54) : mword 64) (STORE (mword_of_int 80 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 9), 8)) apdc_e8a8 apexec_sd80_s1_a0. Qed.

  Lemma api_56 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x56) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x56)%Z (mword_of_int 0xc121 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x56) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 32 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c121 exec_execute_C_BEQZ. Qed.

  Lemma api_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x58) : mword 64) false (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x58)%Z (mword_of_int 0x07000613 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x58) : mword 64) (ITYPE (mword_of_int 112 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 12), ADDI)) apdb_07000613. Qed.

  Lemma api_5c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x5c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x5c)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x5c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma api_5e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x5e) : mword 64) false (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x5e)%Z (mword_of_int 0x06048513 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x5e) : mword 64) (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_06048513. Qed.

  Lemma api_62 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x62) : mword 64) false (JAL (mword_of_int 2093374 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.allocproc + 0x62)%Z (mword_of_int 0x93eff0ef : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x62) : mword 64) (JAL (mword_of_int 2093374 : mword 21, Regidx (mword_of_int 1))) apdb_93eff0ef. Qed.

  Lemma api_66 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x66) : mword 64) false (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 15), AUIPC)).
  Proof. mk_base (KernelSyms.allocproc + 0x66)%Z (mword_of_int 0x00000797 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x66) : mword 64) (UTYPE (mword_of_int 0 : mword 20, Regidx (mword_of_int 15), AUIPC)) apdb_00000797. Qed.

  Lemma api_6a : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x6a) : mword 64) false (ITYPE (mword_of_int 3496 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (KernelSyms.allocproc + 0x6a)%Z (mword_of_int 0xda878793 : mword 32)
    (mword_of_int (KernelSyms.allocproc + 0x6a) : mword 64) (ITYPE (mword_of_int 3496 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) apdb_da878793. Qed.

  Lemma api_6e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x6e) : mword 64) true (STORE (mword_of_int 96 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x6e)%Z (mword_of_int 0xf0bc : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x6e) : mword 64) (STORE (mword_of_int 96 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)) apdc_f0bc apexec_sd96_s1_a5. Qed.

  Lemma api_70 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x70) : mword 64) true (LOAD (mword_of_int 64 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x70)%Z (mword_of_int 0x60bc : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x70) : mword 64) (LOAD (mword_of_int 64 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 8)) apdc_60bc apexec_ld64_s1_a5. Qed.

  Lemma api_72 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x72) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), LUI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x72)%Z (mword_of_int 0x6705 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x72) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 14), LUI)) apdc_6705 exec_execute_C_LUI. Qed.

  Lemma api_74 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x74) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x74)%Z (mword_of_int 0x97ba : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x74) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) cdec_97ba exec_execute_C_ADD. Qed.

  Lemma api_76 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x76) : mword 64) true (STORE (mword_of_int 104 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x76)%Z (mword_of_int 0xf4bc : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x76) : mword 64) (STORE (mword_of_int 104 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)) apdc_f4bc apexec_sd104_s1_a5. Qed.

  Lemma api_78 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x78) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x78)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x78) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma api_7a : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x7a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma api_7c : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x7c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma api_7e : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x7e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma api_80 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x80)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma api_82 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x82)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x82) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma api_84 : kernel_text -∗ instr (mword_of_int (KernelSyms.allocproc + 0x84) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.allocproc + 0x84)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.allocproc + 0x84) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End AllocprocInstrs.

(* CodeArgfd.v -- the instruction-DECODE layer for xv6's argfd().
   For EVERY instruction of

     argfd @ 0x80004a04 .. 0x80004a5c   (offsets 0x00 .. 0x58)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([afi_<off>]).

   The 48-byte frame (0x7179 / f406 / f022 / ec26 / e84a / 1800 ... 70a2 /
   7402 / 64e2 / 6942 / 6145 / 8082) is byte-identical to pipealloc's, and the
   [c.li a0,-1] / [c.ld a5,0(a0)] / [c.sd a5,0(s1)] / [c.j] words are shared
   too, so all of those come from KernelRvcDecode's bit-keyed base.  Four
   compressed words are argfd's alone ([c.mv s1,a2], the two [c.beqz]es, and
   the second [c.j]), as are eight base words.

     0x00 7179       c.addi16sp sp,-48
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 ec26       c.sdsp s1,24(sp)
     0x08 e84a       c.sdsp s2,16(sp)
     0x0a 1800       c.addi4spn s0,sp,48      # s0 = entry sp
     0x0c 892e       c.mv  s2,a1              # s2 := pfd  (callee-saved)
     0x0e 84b2       c.mv  s1,a2              # s1 := pf   (callee-saved)
     0x10 fdc40593   addi  a1,s0,-36          # &fd (upper half of slot 5)
     0x14 dedfd0ef   jal   ra,argint
     0x18 fdc42703   lw    a4,-36(s0)         # a4 := fd
     0x1c 47bd       c.li  a5,15              # NOFILE - 1
     0x1e 02e7ea63   bltu  a5,a4,+0x34        # 15 <u fd -> the -1 tail
     0x22 edffc0ef   jal   ra,myproc
     0x26 fdc42703   lw    a4,-36(s0)
     0x2a 00371793   slli  a5,a4,3
     0x2e 0d078793   addi  a5,a5,208
     0x32 953e       c.add a0,a0,a5           # &p->ofile[fd]
     0x34 611c       c.ld  a5,0(a0)           # f = p->ofile[fd]
     0x36 c385       c.beqz a5,+0x20          # f == 0 -> the other -1 tail
     0x38 00090463   beq   s2,x0,+8           # pfd == 0 -> skip the store
     0x3c 00e92023   sw    a4,0(s2)           # *pfd = fd
     0x40 4501       c.li  a0,0
     0x42 c091       c.beqz s1,+4             # pf == 0 -> skip the store
     0x44 e09c       c.sd  a5,0(s1)           # *pf = f
     0x46 70a2       c.ldsp ra,40(sp)         # <- ALL THREE arms join here
     0x48 7402       c.ldsp s0,32(sp)
     0x4a 64e2       c.ldsp s1,24(sp)
     0x4c 6942       c.ldsp s2,16(sp)
     0x4e 6145       c.addi16sp sp,48
     0x50 8082       c.ret
     0x52 557d       c.li  a0,-1              # the bltu arm
     0x54 bfcd       c.j   -0x0e              # -> +0x46
     0x56 557d       c.li  a0,-1              # the beqz-a5 arm
     0x58 b7fd       c.j   -0x12              # -> +0x46

   Both [c.beqz] arms at +0x38 and +0x42 are the NULL-out-parameter tests;
   the spec's two disequality premises make them fall through, so only the
   fall-through leaves are used and the +0x40/+0x44 skips are never taken.  *)
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
(* Compressed words argfd does not share with any other function.         *)
(* ===================================================================== *)

(* +0x0e  c.mv s1,a2 *)
(* [cdec_84b2] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* +0x36  c.beqz a5,+0x20 *)
Lemma afdc_c385 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc385 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 16, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x42  c.beqz s1,+4 *)
Lemma afdc_c091 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc091 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 2, Cregidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x58  c.j -0x12 -- [cdec_b7fd] (KernelRvcDecode.v; fetchaddr's +0x48 too) *)

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x10  addi a1,s0,-36   (-36 is 0xfdc in the 12-bit field) *)
(* [bdec_fdc40593] -- shared, see KernelBaseDecode.v *)

(* +0x14  jal ra,argint    (0x80004a18 -> 0x80002804 is -8724) *)
Lemma afdb_dedfd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdedfd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2088428 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x18 and +0x26  lw a4,-36(s0) *)
(* [bdec_fdc42703] -- shared, see KernelBaseDecode.v *)

(* +0x1e  bltu a5,a4,+0x34 -- the fused [fd < 0 || fd >= NOFILE] test *)
Lemma afdb_02e7ea63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02e7ea63 : mword 32)) s
  = Some (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* +0x22  jal ra,myproc    (0x80004a26 -> 0x80001904 is -12578) *)
Lemma afdb_edffc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xedffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2084574 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x2a  slli a5,a4,3 *)
Lemma afdb_00371793 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00371793 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLI), s).
Proof. decode_bridge_ms. Qed.

(* +0x38  beq s2,x0,+8 -- the [if (pfd)] test *)
Lemma afdb_00090463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00090463 : mword 32)) s
  = Some (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* +0x3c  sw a4,0(s2) -- *pfd = fd *)
Lemma afdb_00e92023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e92023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 18), 4), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section ArgfdInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  Lemma afi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma afi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma afi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma afi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma afi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma afi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x0a)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  Lemma afi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (KernelSyms.argfd + 0x0c)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma afi_0e : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.argfd + 0x0e)%Z (mword_of_int 0x84b2 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)) cdec_84b2 exec_execute_C_MV. Qed.

  Lemma afi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x10) : mword 64) false (ITYPE (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (KernelSyms.argfd + 0x10)%Z (mword_of_int 0xfdc40593 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x10) : mword 64) (ITYPE (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) bdec_fdc40593. Qed.

  Lemma afi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x14) : mword 64) false (JAL (mword_of_int 2088428 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.argfd + 0x14)%Z (mword_of_int 0xdedfd0ef : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x14) : mword 64) (JAL (mword_of_int 2088428 : mword 21, Regidx (mword_of_int 1))) afdb_dedfd0ef. Qed.

  Lemma afi_18 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x18) : mword 64) false (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (KernelSyms.argfd + 0x18)%Z (mword_of_int 0xfdc42703 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x18) : mword 64) (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) bdec_fdc42703. Qed.

  Lemma afi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x1c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 15 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x1c)%Z (mword_of_int 0x47bd : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 15 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_47bd exec_execute_C_LI. Qed.

  Lemma afi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x1e) : mword 64) false (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (KernelSyms.argfd + 0x1e)%Z (mword_of_int 0x02e7ea63 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x1e) : mword 64) (BTYPE (mword_of_int 52 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)) afdb_02e7ea63. Qed.

  Lemma afi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x22) : mword 64) false (JAL (mword_of_int 2084574 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.argfd + 0x22)%Z (mword_of_int 0xedffc0ef : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x22) : mword 64) (JAL (mword_of_int 2084574 : mword 21, Regidx (mword_of_int 1))) afdb_edffc0ef. Qed.

  Lemma afi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x26) : mword 64) false (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (KernelSyms.argfd + 0x26)%Z (mword_of_int 0xfdc42703 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x26) : mword 64) (LOAD (mword_of_int 0xfdc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) bdec_fdc42703. Qed.

  Lemma afi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x2a) : mword 64) false (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (KernelSyms.argfd + 0x2a)%Z (mword_of_int 0x00371793 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x2a) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 14), Regidx (mword_of_int 15), SLLI)) afdb_00371793. Qed.

  Lemma afi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x2e) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (KernelSyms.argfd + 0x2e)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x2e) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  Lemma afi_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x32) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.argfd + 0x32)%Z (mword_of_int 0x953e : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) cdec_953e exec_execute_C_ADD. Qed.

  Lemma afi_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x34) : mword 64) true (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x34)%Z (mword_of_int 0x611c : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x34) : mword 64) (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) cdec_611c cexec_611c. Qed.

  Lemma afi_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x36) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (KernelSyms.argfd + 0x36)%Z (mword_of_int 0xc385 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x36) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 16 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) afdc_c385 exec_execute_C_BEQZ. Qed.

  Lemma afi_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x38) : mword 64) false (BTYPE (mword_of_int 8 : mword 13, zreg, Regidx (mword_of_int 18), BEQ)).
  Proof. mk_base (KernelSyms.argfd + 0x38)%Z (mword_of_int 0x00090463 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x38) : mword 64) (BTYPE (mword_of_int 8 : mword 13, zreg, Regidx (mword_of_int 18), BEQ)) afdb_00090463. Qed.

  Lemma afi_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x3c) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 18), 4)).
  Proof. mk_base (KernelSyms.argfd + 0x3c)%Z (mword_of_int 0x00e92023 : mword 32)
    (mword_of_int (KernelSyms.argfd + 0x3c) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 18), 4)) afdb_00e92023. Qed.

  Lemma afi_40 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x40) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x40)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x40) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma afi_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x42) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 2 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)).
  Proof. mk_rvc (KernelSyms.argfd + 0x42)%Z (mword_of_int 0xc091 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x42) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 2 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 1)), BEQ)) afdc_c091 exec_execute_C_BEQZ. Qed.

  Lemma afi_44 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x44) : mword 64) true (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x44)%Z (mword_of_int 0xe09c : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x44) : mword 64) (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 8)) cdec_e09c cexec_e09c. Qed.

  Lemma afi_46 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x46) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x46)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma afi_48 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x48) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x48)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x48) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma afi_4a : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x4a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x4a)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x4a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma afi_4c : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x4c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.argfd + 0x4c)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x4c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma afi_4e : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x4e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x4e)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x4e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma afi_50 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x50) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.argfd + 0x50)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x50) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma afi_52 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x52) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x52)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x52) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma afi_54 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x54) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.argfd + 0x54)%Z (mword_of_int 0xbfcd : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x54) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2041 : mword 11) ('b"0")), zreg)) cdec_bfcd exec_execute_C_J. Qed.

  Lemma afi_56 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x56) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (KernelSyms.argfd + 0x56)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x56) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma afi_58 : kernel_text -∗ instr (mword_of_int (KernelSyms.argfd + 0x58) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.argfd + 0x58)%Z (mword_of_int 0xb7fd : mword 16)
    (mword_of_int (KernelSyms.argfd + 0x58) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2039 : mword 11) ('b"0")), zreg)) cdec_b7fd exec_execute_C_J. Qed.

End ArgfdInstrs.

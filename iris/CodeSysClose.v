(* CodeSysClose.v -- the instruction-DECODE layer for xv6's sys_close().
   For EVERY instruction of

     sys_close @ 0x80004cb2 .. 0x80004cf4   (offsets 0x00 .. 0x42)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([sci_<off>]).

   The frame is byte-identical to filedup's 32-byte one (0x1101 / ec06 / e822 /
   1000 ... 60e2 / 6442 / 6105 / 8082), and every other compressed word is in
   KernelRvcDecode's bit-keyed base too, so nothing compressed is cloned here.
   The ten base words are all sys_close's own (three relocated [jal]s, the two
   [addi]s that take the addresses of the locals, the fd reload, the ofile
   displacement, the null store and the [f] reload, plus the [blt]).

     0x00 1101       c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 1000       c.addi4spn s0,sp,32     # s0 = entry sp
     0x08 fe040613   addi  a2,s0,-32         # &f   (frame slot 4)
     0x0c fec40593   addi  a1,s0,-20         # &fd  (upper half of slot 3)
     0x10 4501       c.li  a0,0              # n = 0
     0x12 d41ff0ef   jal   ra,argfd
     0x16 57fd       c.li  a5,-1             # the -1 return, precomputed
     0x18 02054163   blt   a0,x0,+0x22       # argfd < 0 -> the shared tail
     0x1c c37fc0ef   jal   ra,myproc
     0x20 fec42783   lw    a5,-20(s0)        # a5 := fd
     0x24 078e       c.slli a5,a5,3
     0x26 0d078793   addi  a5,a5,208         # 208 + 8*fd
     0x2a 953e       c.add a0,a0,a5          # &p->ofile[fd]
     0x2c 00053023   sd    x0,0(a0)          # p->ofile[fd] = 0
     0x30 fe043503   ld    a0,-32(s0)        # a0 := f
     0x34 b76ff0ef   jal   ra,fileclose
     0x38 4781       c.li  a5,0              # the 0 return
     0x3a 853e       c.mv  a0,a5             # <- both arms join here
     0x3c 60e2       c.ldsp ra,24(sp)
     0x3e 6442       c.ldsp s0,16(sp)
     0x40 6105       c.addi16sp sp,32
     0x42 8082       c.ret

   Note the join at +0x3a: the failure arm's branch lands on the [c.mv],
   which is why the epilogue is proved ONCE and both arms feed it (see
   ProofSysClose's [sc_tail]).                                             *)
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
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all ten are sys_close's own.             *)
(* ===================================================================== *)

(* +0x08  addi a2,s0,-32   (-32 is 0xfe0 in the 12-bit field) *)
Lemma scdb_fe040613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe040613 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x0c  addi a1,s0,-20   (-20 is 0xfec) *)
Lemma scdb_fec40593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfec40593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.


(* +0x18  blt a0,x0,+0x22  -- the [argfd(...) < 0] test *)
Lemma scdb_02054163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02054163 : mword 32)) s
  = Some (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT), s).
Proof. decode_bridge_ms. Qed.

(* +0x1c  jal ra,myproc    (0x80004cce -> 0x80001904 is -13258) *)
Lemma scdb_c37fc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc37fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2083894 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x20  lw a5,-20(s0) *)
Lemma scdb_fec42783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfec42783 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x26  addi a5,a5,208 -- [bdec_0d078793] (KernelBaseDecode.v) *)


(* +0x30  ld a0,-32(s0) *)
Lemma scdb_fe043503 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe043503 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8), s).
Proof. decode_bridge_ms. Qed.

(* +0x34  jal ra,fileclose (0x80004ce6 -> 0x8000405c is -3210) *)
Lemma scdb_b76ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb76ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093942 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysCloseInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation SC := KernelSyms.sys_close.

  Lemma sci_00 : kernel_text -∗ instr (mword_of_int (SC + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (SC + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (SC + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma sci_02 : kernel_text -∗ instr (mword_of_int (SC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SC + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (SC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma sci_04 : kernel_text -∗ instr (mword_of_int (SC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SC + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (SC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma sci_06 : kernel_text -∗ instr (mword_of_int (SC + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SC + 0x06)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (SC + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma sci_08 : kernel_text -∗ instr (mword_of_int (SC + 0x08) : mword 64) false (ITYPE (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)).
  Proof. mk_base (SC + 0x08)%Z (mword_of_int 0xfe040613 : mword 32)
    (mword_of_int (SC + 0x08) : mword 64) (ITYPE (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 12), ADDI)) scdb_fe040613. Qed.

  Lemma sci_0c : kernel_text -∗ instr (mword_of_int (SC + 0x0c) : mword 64) false (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SC + 0x0c)%Z (mword_of_int 0xfec40593 : mword 32)
    (mword_of_int (SC + 0x0c) : mword 64) (ITYPE (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) scdb_fec40593. Qed.

  Lemma sci_10 : kernel_text -∗ instr (mword_of_int (SC + 0x10) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SC + 0x10)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SC + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma sci_12 : kernel_text -∗ instr (mword_of_int (SC + 0x12) : mword 64) false (JAL (mword_of_int 2096448 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x12)%Z (mword_of_int 0xd41ff0ef : mword 32)
    (mword_of_int (SC + 0x12) : mword 64) (JAL (mword_of_int 2096448 : mword 21, Regidx (mword_of_int 1))) bdec_d41ff0ef. Qed.

  Lemma sci_16 : kernel_text -∗ instr (mword_of_int (SC + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SC + 0x16)%Z (mword_of_int 0x57fd : mword 16)
    (mword_of_int (SC + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_57fd exec_execute_C_LI. Qed.

  Lemma sci_18 : kernel_text -∗ instr (mword_of_int (SC + 0x18) : mword 64) false (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)).
  Proof. mk_base (SC + 0x18)%Z (mword_of_int 0x02054163 : mword 32)
    (mword_of_int (SC + 0x18) : mword 64) (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 10), BLT)) scdb_02054163. Qed.

  Lemma sci_1c : kernel_text -∗ instr (mword_of_int (SC + 0x1c) : mword 64) false (JAL (mword_of_int 2083894 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x1c)%Z (mword_of_int 0xc37fc0ef : mword 32)
    (mword_of_int (SC + 0x1c) : mword 64) (JAL (mword_of_int 2083894 : mword 21, Regidx (mword_of_int 1))) scdb_c37fc0ef. Qed.

  Lemma sci_20 : kernel_text -∗ instr (mword_of_int (SC + 0x20) : mword 64) false (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SC + 0x20)%Z (mword_of_int 0xfec42783 : mword 32)
    (mword_of_int (SC + 0x20) : mword 64) (LOAD (mword_of_int 0xfec : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) scdb_fec42783. Qed.

  Lemma sci_24 : kernel_text -∗ instr (mword_of_int (SC + 0x24) : mword 64) true (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SC + 0x24)%Z (mword_of_int 0x078e : mword 16)
    (mword_of_int (SC + 0x24) : mword 64) (SHIFTIOP (mword_of_int 3 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_078e exec_execute_C_SLLI. Qed.

  Lemma sci_26 : kernel_text -∗ instr (mword_of_int (SC + 0x26) : mword 64) false (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_base (SC + 0x26)%Z (mword_of_int 0x0d078793 : mword 32)
    (mword_of_int (SC + 0x26) : mword 64) (ITYPE (mword_of_int 208 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) bdec_0d078793. Qed.

  Lemma sci_2a : kernel_text -∗ instr (mword_of_int (SC + 0x2a) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SC + 0x2a)%Z (mword_of_int 0x953e : mword 16)
    (mword_of_int (SC + 0x2a) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADD)) cdec_953e exec_execute_C_ADD. Qed.

  Lemma sci_2c : kernel_text -∗ instr (mword_of_int (SC + 0x2c) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (SC + 0x2c)%Z (mword_of_int 0x00053023 : mword 32)
    (mword_of_int (SC + 0x2c) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)) bdec_00053023. Qed.

  Lemma sci_30 : kernel_text -∗ instr (mword_of_int (SC + 0x30) : mword 64) false (LOAD (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_base (SC + 0x30)%Z (mword_of_int 0xfe043503 : mword 32)
    (mword_of_int (SC + 0x30) : mword 64) (LOAD (mword_of_int 0xfe0 : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 10), false, 8)) scdb_fe043503. Qed.

  Lemma sci_34 : kernel_text -∗ instr (mword_of_int (SC + 0x34) : mword 64) false (JAL (mword_of_int 2093942 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x34)%Z (mword_of_int 0xb76ff0ef : mword 32)
    (mword_of_int (SC + 0x34) : mword 64) (JAL (mword_of_int 2093942 : mword 21, Regidx (mword_of_int 1))) scdb_b76ff0ef. Qed.

  Lemma sci_38 : kernel_text -∗ instr (mword_of_int (SC + 0x38) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (SC + 0x38)%Z (mword_of_int 0x4781 : mword 16)
    (mword_of_int (SC + 0x38) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4781 exec_execute_C_LI. Qed.

  Lemma sci_3a : kernel_text -∗ instr (mword_of_int (SC + 0x3a) : mword 64) true (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SC + 0x3a)%Z (mword_of_int 0x853e : mword 16)
    (mword_of_int (SC + 0x3a) : mword 64) (RTYPE (Regidx (mword_of_int 15), zreg, Regidx (mword_of_int 10), ADD)) cdec_853e exec_execute_C_MV. Qed.

  Lemma sci_3c : kernel_text -∗ instr (mword_of_int (SC + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SC + 0x3c)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (SC + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma sci_3e : kernel_text -∗ instr (mword_of_int (SC + 0x3e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SC + 0x3e)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (SC + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma sci_40 : kernel_text -∗ instr (mword_of_int (SC + 0x40) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SC + 0x40)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (SC + 0x40) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma sci_42 : kernel_text -∗ instr (mword_of_int (SC + 0x42) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SC + 0x42)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SC + 0x42) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End SysCloseInstrs.

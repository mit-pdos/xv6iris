(* WpSysPauseDecode.v -- the instruction-DECODE layer for xv6's sys_pause().
   For EVERY instruction of

     sys_pause @ 0x800029b0 .. 0x80002a50   (offsets 0x00 .. 0xa0)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([spi_<off>]).

     +0x00  7139        c.addi16sp sp,-64      64-byte (8-slot) frame
     +0x02  fc06        c.sdsp   ra,56(sp)
     +0x04  f822        c.sdsp   s0,48(sp)
     +0x06  0080        c.addi4spn s0,sp,64    s0 = entry sp
     +0x08  fcc40593    addi     a1,s0,-52     &n  (UPPER half of slot 7)
     +0x0c  4501        c.li     a0,0
     +0x0e  e47ff0ef    jal      ra,argint
     +0x12  fcc42783    lw       a5,-52(s0)
     +0x16  0607c863    blt      a5,x0,+0x70   the [n < 0] fixup
     +0x1a  00015517    auipc    a0,0x15       <-- the fixup's back edge lands here
     +0x1e  7ae50513    addi     a0,a0,1966    a0 = &tickslock
     +0x22  a36fe0ef    jal      ra,acquire
     +0x26  fcc42783    lw       a5,-52(s0)
     +0x2a  c3b9        c.beqz   a5,+0x46      n == 0 skips the loop entirely
     +0x2c  f426        c.sdsp   s1,40(sp)     s1/s2/s3 saved on the LOOP path only
     +0x2e  f04a        c.sdsp   s2,32(sp)
     +0x30  ec4e        c.sdsp   s3,24(sp)
     +0x32  00008997    auipc    s3,0x8
     +0x36  8669a983    lw       s3,-1946(s3)  ticks0 = ticks (under the lock)
     +0x3a  00015917    auipc    s2,0x15
     +0x3e  78e90913    addi     s2,s2,1934    s2 = &tickslock
     +0x42  00008497    auipc    s1,0x8
     +0x46  85648493    addi     s1,s1,-1962   s1 = &ticks
     +0x4a  f0bfe0ef    jal      ra,myproc     <-- LOOP HEAD
     +0x4e  f44ff0ef    jal      ra,killed
     +0x52  ed0d        c.bnez   a0,+0x3a      killed -> the -1 exit
     +0x54  85ca        c.mv     a1,s2
     +0x56  8526        c.mv     a0,s1
     +0x58  cfeff0ef    jal      ra,sleep
     +0x5c  409c        c.lw     a5,0(s1)      a5 = ticks
     +0x5e  413787bb    subw     a5,a5,s3      a5 = ticks - ticks0
     +0x62  fcc42703    lw       a4,-52(s0)    a4 = n
     +0x66  fee7e2e3    bltu     a5,a4,-0x1c   back edge to the loop head
     +0x6a  74a2        c.ldsp   s1,40(sp)
     +0x6c  7902        c.ldsp   s2,32(sp)
     +0x6e  69e2        c.ldsp   s3,24(sp)
     +0x70  00015517    auipc    a0,0x15       <-- the c.beqz's target
     +0x74  75850513    addi     a0,a0,1880
     +0x78  a68fe0ef    jal      ra,release
     +0x7c  4501        c.li     a0,0
     +0x7e  70e2        c.ldsp   ra,56(sp)     <-- the SHARED epilogue
     +0x80  7442        c.ldsp   s0,48(sp)
     +0x82  6121        c.addi16sp sp,64
     +0x84  8082        c.ret
     +0x86  fc042623    sw       zero,-52(s0)  the [n < 0] fixup: n = 0 ...
     +0x8a  bf41        c.j      -0x70         ... and back to +0x1a
     +0x8c  00015517    auipc    a0,0x15       <-- the c.bnez's target
     +0x90  73c50513    addi     a0,a0,1852
     +0x94  a4cfe0ef    jal      ra,release
     +0x98  557d        c.li     a0,-1
     +0x9a  74a2        c.ldsp   s1,40(sp)
     +0x9c  7902        c.ldsp   s2,32(sp)
     +0x9e  69e2        c.ldsp   s3,24(sp)
     +0xa0  bff9        c.j      -0x22         rejoin the epilogue at +0x7e

   Every compressed word is in KernelRvcDecode's bit-keyed base (the five
   sys_pause needed -- 409c / c3b9 / ed0d / bf41 / bff9 -- were added there,
   since a bit pattern is address-independent).  All the base words except the
   twice-shared [auipc a0,0x15] are sys_pause's own: the four relocated
   auipc/addi pairs, five jals, three [-52(s0)] accesses, the two branches and
   the [subw].                                                              *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvTryStep RiscvFetchExec.
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
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* +0x08  addi a1,s0,-52   (-52 is 0xfcc in the 12-bit field) *)
Lemma spdb_fcc40593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfcc40593 : mword 32)) s
  = Some (ITYPE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x0e  jal ra,argint    (0x800029be -> 0x80002804 is -442) *)
Lemma spdb_e47ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe47ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096710 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x12 / +0x26  lw a5,-52(s0) *)
Lemma spdb_fcc42783 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfcc42783 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x16  blt a5,x0,+0x70 -- the [n < 0] test *)
Lemma spdb_0607c863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0607c863 : mword 32)) s
  = Some (BTYPE (mword_of_int 112 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT), s).
Proof. decode_bridge_ms. Qed.

(* +0x1e  addi a0,a0,1966  -- a0 := &tickslock *)
Lemma spdb_7ae50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x7ae50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x7ae : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x22  jal ra,acquire   (0x800029d2 -> 0x80000c08 is -7626) *)
Lemma spdb_a36fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa36fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089526 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x32  auipc s3,0x8 *)
Lemma spdb_00008997 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00008997 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 19), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x36  lw s3,-1946(s3)  -- ticks0 := ticks *)
Lemma spdb_8669a983 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x8669a983 : mword 32)) s
  = Some (LOAD (mword_of_int 0x866 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x3a  auipc s2,0x15 *)
Lemma spdb_00015917 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00015917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x3e  addi s2,s2,1934  -- s2 := &tickslock *)
Lemma spdb_78e90913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x78e90913 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x78e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x42  auipc s1,0x8 *)
Lemma spdb_00008497 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00008497 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* +0x46  addi s1,s1,-1962 -- s1 := &ticks *)
Lemma spdb_85648493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x85648493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x856 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x4a  jal ra,myproc    (0x800029fa -> 0x80001904 is -4342) *)
Lemma spdb_f0bfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf0bfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092810 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x4e  jal ra,killed    (0x800029fe -> 0x80002142 is -2236) *)
Lemma spdb_f44ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf44ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094916 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x58  jal ra,sleep     (0x80002a08 -> 0x80001f06 is -2818) *)
Lemma spdb_cfeff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xcfeff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094334 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x5e  subw a5,a5,s3 *)
Lemma spdb_413787bb s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x413787bb : mword 32)) s
  = Some (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SUBW), s).
Proof. decode_bridge_ms. Qed.

(* +0x62  lw a4,-52(s0) *)
Lemma spdb_fcc42703 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfcc42703 : mword 32)) s
  = Some (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x66  bltu a5,a4,-0x1c -- the loop's back edge *)
Lemma spdb_fee7e2e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfee7e2e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* +0x74  addi a0,a0,1880  -- a0 := &tickslock (normal exit) *)
Lemma spdb_75850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x75850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x758 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x78  jal ra,release   (0x80002a28 -> 0x80000c90 is -7576) *)
Lemma spdb_a68fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa68fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089576 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* +0x86  sw zero,-52(s0)  -- the [n < 0] fixup *)
Lemma spdb_fc042623 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc042623 : mword 32)) s
  = Some (STORE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 8), 4), s).
Proof. decode_bridge_ms. Qed.

(* +0x90  addi a0,a0,1852  -- a0 := &tickslock (killed exit) *)
Lemma spdb_73c50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x73c50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x73c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* +0x94  jal ra,release   (0x80002a44 -> 0x80000c90 is -7604) *)
Lemma spdb_a4cfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xa4cfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2089548 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section SysPauseInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation SP := KernelSyms.sys_pause.

  (* ---- prologue: the 64-byte (8-slot) frame ---- *)
  Lemma spi_00 : kernel_text -∗ instr (mword_of_int (SP + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SP + 0x00)%Z (mword_of_int 0x7139 : mword 16)
    (mword_of_int (SP + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  Lemma spi_02 : kernel_text -∗ instr (mword_of_int (SP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SP + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (SP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  Lemma spi_04 : kernel_text -∗ instr (mword_of_int (SP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SP + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (SP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  Lemma spi_06 : kernel_text -∗ instr (mword_of_int (SP + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SP + 0x06)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (SP + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  (* ---- argint(0, &n) ---- *)
  Lemma spi_08 : kernel_text -∗ instr (mword_of_int (SP + 0x08) : mword 64) false (ITYPE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SP + 0x08)%Z (mword_of_int 0xfcc40593 : mword 32)
    (mword_of_int (SP + 0x08) : mword 64) (ITYPE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 11), ADDI)) spdb_fcc40593. Qed.

  Lemma spi_0c : kernel_text -∗ instr (mword_of_int (SP + 0x0c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SP + 0x0c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SP + 0x0c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  Lemma spi_0e : kernel_text -∗ instr (mword_of_int (SP + 0x0e) : mword 64) false (JAL (mword_of_int 2096710 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x0e)%Z (mword_of_int 0xe47ff0ef : mword 32)
    (mword_of_int (SP + 0x0e) : mword 64) (JAL (mword_of_int 2096710 : mword 21, Regidx (mword_of_int 1))) spdb_e47ff0ef. Qed.

  (* ---- the [n < 0] test ---- *)
  Lemma spi_12 : kernel_text -∗ instr (mword_of_int (SP + 0x12) : mword 64) false (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SP + 0x12)%Z (mword_of_int 0xfcc42783 : mword 32)
    (mword_of_int (SP + 0x12) : mword 64) (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) spdb_fcc42783. Qed.

  Lemma spi_16 : kernel_text -∗ instr (mword_of_int (SP + 0x16) : mword 64) false (BTYPE (mword_of_int 112 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)).
  Proof. mk_base (SP + 0x16)%Z (mword_of_int 0x0607c863 : mword 32)
    (mword_of_int (SP + 0x16) : mword 64) (BTYPE (mword_of_int 112 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 15), BLT)) spdb_0607c863. Qed.

  (* ---- acquire(&tickslock) ---- *)
  Lemma spi_1a : kernel_text -∗ instr (mword_of_int (SP + 0x1a) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (SP + 0x1a)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (SP + 0x1a) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma spi_1e : kernel_text -∗ instr (mword_of_int (SP + 0x1e) : mword 64) false (ITYPE (mword_of_int 0x7ae : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SP + 0x1e)%Z (mword_of_int 0x7ae50513 : mword 32)
    (mword_of_int (SP + 0x1e) : mword 64) (ITYPE (mword_of_int 0x7ae : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) spdb_7ae50513. Qed.

  Lemma spi_22 : kernel_text -∗ instr (mword_of_int (SP + 0x22) : mword 64) false (JAL (mword_of_int 2089526 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x22)%Z (mword_of_int 0xa36fe0ef : mword 32)
    (mword_of_int (SP + 0x22) : mword 64) (JAL (mword_of_int 2089526 : mword 21, Regidx (mword_of_int 1))) spdb_a36fe0ef. Qed.

  (* ---- the [n == 0] test ---- *)
  Lemma spi_26 : kernel_text -∗ instr (mword_of_int (SP + 0x26) : mword 64) false (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (SP + 0x26)%Z (mword_of_int 0xfcc42783 : mword 32)
    (mword_of_int (SP + 0x26) : mword 64) (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 15), false, 4)) spdb_fcc42783. Qed.

  Lemma spi_2a : kernel_text -∗ instr (mword_of_int (SP + 0x2a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 35 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (SP + 0x2a)%Z (mword_of_int 0xc3b9 : mword 16)
    (mword_of_int (SP + 0x2a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 35 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_c3b9 exec_execute_C_BEQZ. Qed.

  (* ---- the loop-path saves of s1/s2/s3 ---- *)
  Lemma spi_2c : kernel_text -∗ instr (mword_of_int (SP + 0x2c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SP + 0x2c)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (SP + 0x2c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  Lemma spi_2e : kernel_text -∗ instr (mword_of_int (SP + 0x2e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (SP + 0x2e)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (SP + 0x2e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  Lemma spi_30 : kernel_text -∗ instr (mword_of_int (SP + 0x30) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (SP + 0x30)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (SP + 0x30) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  (* ---- ticks0 := ticks; s2 := &tickslock; s1 := &ticks ---- *)
  Lemma spi_32 : kernel_text -∗ instr (mword_of_int (SP + 0x32) : mword 64) false (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 19), AUIPC)).
  Proof. mk_base (SP + 0x32)%Z (mword_of_int 0x00008997 : mword 32)
    (mword_of_int (SP + 0x32) : mword 64) (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 19), AUIPC)) spdb_00008997. Qed.

  Lemma spi_36 : kernel_text -∗ instr (mword_of_int (SP + 0x36) : mword 64) false (LOAD (mword_of_int 0x866 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), false, 4)).
  Proof. mk_base (SP + 0x36)%Z (mword_of_int 0x8669a983 : mword 32)
    (mword_of_int (SP + 0x36) : mword 64) (LOAD (mword_of_int 0x866 : mword 12, Regidx (mword_of_int 19), Regidx (mword_of_int 19), false, 4)) spdb_8669a983. Qed.

  Lemma spi_3a : kernel_text -∗ instr (mword_of_int (SP + 0x3a) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (SP + 0x3a)%Z (mword_of_int 0x00015917 : mword 32)
    (mword_of_int (SP + 0x3a) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 18), AUIPC)) spdb_00015917. Qed.

  Lemma spi_3e : kernel_text -∗ instr (mword_of_int (SP + 0x3e) : mword 64) false (ITYPE (mword_of_int 0x78e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (SP + 0x3e)%Z (mword_of_int 0x78e90913 : mword 32)
    (mword_of_int (SP + 0x3e) : mword 64) (ITYPE (mword_of_int 0x78e : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) spdb_78e90913. Qed.

  Lemma spi_42 : kernel_text -∗ instr (mword_of_int (SP + 0x42) : mword 64) false (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (SP + 0x42)%Z (mword_of_int 0x00008497 : mword 32)
    (mword_of_int (SP + 0x42) : mword 64) (UTYPE (mword_of_int 0x8 : mword 20, Regidx (mword_of_int 9), AUIPC)) spdb_00008497. Qed.

  Lemma spi_46 : kernel_text -∗ instr (mword_of_int (SP + 0x46) : mword 64) false (ITYPE (mword_of_int 0x856 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (SP + 0x46)%Z (mword_of_int 0x85648493 : mword 32)
    (mword_of_int (SP + 0x46) : mword 64) (ITYPE (mword_of_int 0x856 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) spdb_85648493. Qed.

  (* ---- the wait loop ---- *)
  Lemma spi_4a : kernel_text -∗ instr (mword_of_int (SP + 0x4a) : mword 64) false (JAL (mword_of_int 2092810 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x4a)%Z (mword_of_int 0xf0bfe0ef : mword 32)
    (mword_of_int (SP + 0x4a) : mword 64) (JAL (mword_of_int 2092810 : mword 21, Regidx (mword_of_int 1))) spdb_f0bfe0ef. Qed.

  Lemma spi_4e : kernel_text -∗ instr (mword_of_int (SP + 0x4e) : mword 64) false (JAL (mword_of_int 2094916 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x4e)%Z (mword_of_int 0xf44ff0ef : mword 32)
    (mword_of_int (SP + 0x4e) : mword 64) (JAL (mword_of_int 2094916 : mword 21, Regidx (mword_of_int 1))) spdb_f44ff0ef. Qed.

  Lemma spi_52 : kernel_text -∗ instr (mword_of_int (SP + 0x52) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)).
  Proof. mk_rvc (SP + 0x52)%Z (mword_of_int 0xed0d : mword 16)
    (mword_of_int (SP + 0x52) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 29 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BNE)) cdec_ed0d exec_execute_C_BNEZ. Qed.

  Lemma spi_54 : kernel_text -∗ instr (mword_of_int (SP + 0x54) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (SP + 0x54)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (SP + 0x54) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma spi_56 : kernel_text -∗ instr (mword_of_int (SP + 0x56) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SP + 0x56)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SP + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma spi_58 : kernel_text -∗ instr (mword_of_int (SP + 0x58) : mword 64) false (JAL (mword_of_int 2094334 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x58)%Z (mword_of_int 0xcfeff0ef : mword 32)
    (mword_of_int (SP + 0x58) : mword 64) (JAL (mword_of_int 2094334 : mword 21, Regidx (mword_of_int 1))) spdb_cfeff0ef. Qed.

  Lemma spi_5c : kernel_text -∗ instr (mword_of_int (SP + 0x5c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (SP + 0x5c)%Z (mword_of_int 0x409c : mword 16)
    (mword_of_int (SP + 0x5c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) cdec_409c exec_execute_C_LW. Qed.

  Lemma spi_5e : kernel_text -∗ instr (mword_of_int (SP + 0x5e) : mword 64) false (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SUBW)).
  Proof. mk_base (SP + 0x5e)%Z (mword_of_int 0x413787bb : mword 32)
    (mword_of_int (SP + 0x5e) : mword 64) (RTYPEW (Regidx (mword_of_int 19), Regidx (mword_of_int 15), Regidx (mword_of_int 15), SUBW)) spdb_413787bb. Qed.

  Lemma spi_62 : kernel_text -∗ instr (mword_of_int (SP + 0x62) : mword 64) false (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)).
  Proof. mk_base (SP + 0x62)%Z (mword_of_int 0xfcc42703 : mword 32)
    (mword_of_int (SP + 0x62) : mword 64) (LOAD (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 8), Regidx (mword_of_int 14), false, 4)) spdb_fcc42703. Qed.

  Lemma spi_66 : kernel_text -∗ instr (mword_of_int (SP + 0x66) : mword 64) false (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)).
  Proof. mk_base (SP + 0x66)%Z (mword_of_int 0xfee7e2e3 : mword 32)
    (mword_of_int (SP + 0x66) : mword 64) (BTYPE (mword_of_int 8164 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 15), BLTU)) spdb_fee7e2e3. Qed.

  (* ---- loop-path restores of s1/s2/s3 ---- *)
  Lemma spi_6a : kernel_text -∗ instr (mword_of_int (SP + 0x6a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SP + 0x6a)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (SP + 0x6a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  Lemma spi_6c : kernel_text -∗ instr (mword_of_int (SP + 0x6c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SP + 0x6c)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (SP + 0x6c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  Lemma spi_6e : kernel_text -∗ instr (mword_of_int (SP + 0x6e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (SP + 0x6e)%Z (mword_of_int 0x69e2 : mword 16)
    (mword_of_int (SP + 0x6e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.

  (* ---- the normal (0) exit ---- *)
  Lemma spi_70 : kernel_text -∗ instr (mword_of_int (SP + 0x70) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (SP + 0x70)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (SP + 0x70) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma spi_74 : kernel_text -∗ instr (mword_of_int (SP + 0x74) : mword 64) false (ITYPE (mword_of_int 0x758 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SP + 0x74)%Z (mword_of_int 0x75850513 : mword 32)
    (mword_of_int (SP + 0x74) : mword 64) (ITYPE (mword_of_int 0x758 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) spdb_75850513. Qed.

  Lemma spi_78 : kernel_text -∗ instr (mword_of_int (SP + 0x78) : mword 64) false (JAL (mword_of_int 2089576 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x78)%Z (mword_of_int 0xa68fe0ef : mword 32)
    (mword_of_int (SP + 0x78) : mword 64) (JAL (mword_of_int 2089576 : mword 21, Regidx (mword_of_int 1))) spdb_a68fe0ef. Qed.

  Lemma spi_7c : kernel_text -∗ instr (mword_of_int (SP + 0x7c) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SP + 0x7c)%Z (mword_of_int 0x4501 : mword 16)
    (mword_of_int (SP + 0x7c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_4501 exec_execute_C_LI. Qed.

  (* ---- the shared epilogue ---- *)
  Lemma spi_7e : kernel_text -∗ instr (mword_of_int (SP + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (SP + 0x7e)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (SP + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  Lemma spi_80 : kernel_text -∗ instr (mword_of_int (SP + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (SP + 0x80)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (SP + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  Lemma spi_82 : kernel_text -∗ instr (mword_of_int (SP + 0x82) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SP + 0x82)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (SP + 0x82) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  Lemma spi_84 : kernel_text -∗ instr (mword_of_int (SP + 0x84) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (SP + 0x84)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (SP + 0x84) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- the [n < 0] fixup ---- *)
  Lemma spi_86 : kernel_text -∗ instr (mword_of_int (SP + 0x86) : mword 64) false (STORE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 8), 4)).
  Proof. mk_base (SP + 0x86)%Z (mword_of_int 0xfc042623 : mword 32)
    (mword_of_int (SP + 0x86) : mword 64) (STORE (mword_of_int 0xfcc : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 8), 4)) spdb_fc042623. Qed.

  Lemma spi_8a : kernel_text -∗ instr (mword_of_int (SP + 0x8a) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1992 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SP + 0x8a)%Z (mword_of_int 0xbf41 : mword 16)
    (mword_of_int (SP + 0x8a) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1992 : mword 11) ('b"0")), zreg)) cdec_bf41 exec_execute_C_J. Qed.

  (* ---- the killed (-1) exit ---- *)
  Lemma spi_8c : kernel_text -∗ instr (mword_of_int (SP + 0x8c) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (SP + 0x8c)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (SP + 0x8c) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma spi_90 : kernel_text -∗ instr (mword_of_int (SP + 0x90) : mword 64) false (ITYPE (mword_of_int 0x73c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (SP + 0x90)%Z (mword_of_int 0x73c50513 : mword 32)
    (mword_of_int (SP + 0x90) : mword 64) (ITYPE (mword_of_int 0x73c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) spdb_73c50513. Qed.

  Lemma spi_94 : kernel_text -∗ instr (mword_of_int (SP + 0x94) : mword 64) false (JAL (mword_of_int 2089548 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SP + 0x94)%Z (mword_of_int 0xa4cfe0ef : mword 32)
    (mword_of_int (SP + 0x94) : mword 64) (JAL (mword_of_int 2089548 : mword 21, Regidx (mword_of_int 1))) spdb_a4cfe0ef. Qed.

  Lemma spi_98 : kernel_text -∗ instr (mword_of_int (SP + 0x98) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)).
  Proof. mk_rvc (SP + 0x98)%Z (mword_of_int 0x557d : mword 16)
    (mword_of_int (SP + 0x98) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), zreg, Regidx (mword_of_int 10), ADDI)) cdec_557d exec_execute_C_LI. Qed.

  Lemma spi_9a : kernel_text -∗ instr (mword_of_int (SP + 0x9a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (SP + 0x9a)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (SP + 0x9a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  Lemma spi_9c : kernel_text -∗ instr (mword_of_int (SP + 0x9c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (SP + 0x9c)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (SP + 0x9c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  Lemma spi_9e : kernel_text -∗ instr (mword_of_int (SP + 0x9e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (SP + 0x9e)%Z (mword_of_int 0x69e2 : mword 16)
    (mword_of_int (SP + 0x9e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.

  Lemma spi_a0 : kernel_text -∗ instr (mword_of_int (SP + 0xa0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SP + 0xa0)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (SP + 0xa0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

End SysPauseInstrs.

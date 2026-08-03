(* CodeBpin.v -- the instruction-DECODE layer for xv6's bpin() AND
   bunpin().  ONE file for the pair: the two functions are the same twenty
   instructions (the standard 32-byte frame, a0 := &bcache, jal acquire,
   lw/addiw/sw of b->refcnt, a0 := &bcache, jal release, epilogue), differing
   only in their entry address, their four relocated immediates and the sign
   of the [c.addiw].  Sharing the file also shares the three new compressed
   words ([c.lw a5,64(s1)] / [c.sw a5,64(s1)] / [c.addiw a5,-1]) instead of
   cloning them per function.

     bpin   @ 0x80002cc2 .. 0x80002cf4   (offsets 0x00 .. 0x32)
     bunpin @ 0x80002cf6 .. 0x80002d28   (offsets 0x00 .. 0x32)

   For every instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([bpi_<off>] / [bui_<off>]).  Everything in the frame prologue /
   epilogue is already shared in KernelRvcDecode's bit-keyed base and nothing
   compressed from there is cloned.

     bpin                                    bunpin
     0x00 1101       c.addi sp,sp,-32        1101
     0x02 ec06       c.sdsp ra,24(sp)        ec06
     0x04 e822       c.sdsp s0,16(sp)        e822
     0x06 e426       c.sdsp s1,8(sp)         e426
     0x08 1000       c.addi4spn s0,sp,32     1000
     0x0a 84aa       c.mv  s1,a0             84aa
     0x0c 00015517   auipc a0,0x15           00015517
     0x10 4c250513   addi  a0,a0,1218        48e50513   # a0 := &bcache
     0x14 f33fd0ef   jal   ra,acquire        efffd0ef
     0x18 40bc       c.lw  a5,64(s1)         40bc       # a5 := b->refcnt
     0x1a 2785       c.addiw a5,a5,1         37fd       # +/- 1
     0x1c c0bc       c.sw  a5,64(s1)         c0bc       # b->refcnt = a5
     0x1e 00015517   auipc a0,0x15           00015517
     0x22 4b050513   addi  a0,a0,1200        47c50513   # a0 := &bcache
     0x26 fa9fd0ef   jal   ra,release        f75fd0ef
     0x2a 60e2       c.ldsp ra,24(sp)        60e2
     0x2c 6442       c.ldsp s0,16(sp)        6442
     0x2e 64a2       c.ldsp s1,8(sp)         64a2
     0x30 6105       c.addi16sp sp,32        6105
     0x32 8082       c.ret                   8082

   Every compressed word of this pair is shared with another function, so all
   of them come from KernelRvcDecode.v: 0x40bc / 0xc0bc (with their leaf-form
   expansions [cexec_40bc] / [cexec_c0bc]) from the [b->refcnt] read/write
   that bread and brelse also perform, and 0x37fd ([c.addiw a5,-1]) from
   brelse's [refcnt--] and pop_off's [c->noff--].                           *)
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
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

Lemma bpdb_4c250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4c250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x4c2 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_4b050513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4b050513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x4b0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_48e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x48e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x48e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_47c50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x47c50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x47c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* the four calls: bpin/bunpin x acquire/release *)
Lemma bpdb_f33fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf33fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fdf32 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_fa9fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfa9fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fdfa8 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_efffd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xefffd0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fdefe : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma bpdb_f75fd0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf75fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fdf74 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* The compressed words this pair steps -- 0x40bc / 0xc0bc / 0x37fd and the
   two leaf-form expansions -- all come from KernelRvcDecode.v. *)

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section BpinInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Notation BP := KernelSyms.bpin.
  Notation BU := KernelSyms.bunpin.

  (* ---- bpin ---- *)

  Lemma bpi_00 : kernel_text -∗ instr (mword_of_int (BP + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (BP + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (BP + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma bpi_02 : kernel_text -∗ instr (mword_of_int (BP + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BP + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (BP + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma bpi_04 : kernel_text -∗ instr (mword_of_int (BP + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BP + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (BP + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma bpi_06 : kernel_text -∗ instr (mword_of_int (BP + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BP + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (BP + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma bpi_08 : kernel_text -∗ instr (mword_of_int (BP + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BP + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (BP + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma bpi_0a : kernel_text -∗ instr (mword_of_int (BP + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (BP + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (BP + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma bpi_0c : kernel_text -∗ instr (mword_of_int (BP + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BP + 0x0c)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BP + 0x0c) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bpi_10 : kernel_text -∗ instr (mword_of_int (BP + 0x10) : mword 64) false (ITYPE (mword_of_int 0x4c2 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BP + 0x10)%Z (mword_of_int 0x4c250513 : mword 32)
    (mword_of_int (BP + 0x10) : mword 64) (ITYPE (mword_of_int 0x4c2 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bpdb_4c250513. Qed.

  Lemma bpi_14 : kernel_text -∗ instr (mword_of_int (BP + 0x14) : mword 64) false (JAL (mword_of_int 0x1fdf32 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BP + 0x14)%Z (mword_of_int 0xf33fd0ef : mword 32)
    (mword_of_int (BP + 0x14) : mword 64) (JAL (mword_of_int 0x1fdf32 : mword 21, Regidx (mword_of_int 1))) bpdb_f33fd0ef. Qed.

  Lemma bpi_18 : kernel_text -∗ instr (mword_of_int (BP + 0x18) : mword 64) true (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BP + 0x18)%Z (mword_of_int 0x40bc : mword 16)
    (mword_of_int (BP + 0x18) : mword 64) (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40bc cexec_40bc. Qed.

  Lemma bpi_1a : kernel_text -∗ instr (mword_of_int (BP + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (BP + 0x1a)%Z (mword_of_int 0x2785 : mword 16)
    (mword_of_int (BP + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2785 exec_execute_C_ADDIW. Qed.

  Lemma bpi_1c : kernel_text -∗ instr (mword_of_int (BP + 0x1c) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (BP + 0x1c)%Z (mword_of_int 0xc0bc : mword 16)
    (mword_of_int (BP + 0x1c) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0bc cexec_c0bc. Qed.

  Lemma bpi_1e : kernel_text -∗ instr (mword_of_int (BP + 0x1e) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BP + 0x1e)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BP + 0x1e) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bpi_22 : kernel_text -∗ instr (mword_of_int (BP + 0x22) : mword 64) false (ITYPE (mword_of_int 0x4b0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BP + 0x22)%Z (mword_of_int 0x4b050513 : mword 32)
    (mword_of_int (BP + 0x22) : mword 64) (ITYPE (mword_of_int 0x4b0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bpdb_4b050513. Qed.

  Lemma bpi_26 : kernel_text -∗ instr (mword_of_int (BP + 0x26) : mword 64) false (JAL (mword_of_int 0x1fdfa8 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BP + 0x26)%Z (mword_of_int 0xfa9fd0ef : mword 32)
    (mword_of_int (BP + 0x26) : mword 64) (JAL (mword_of_int 0x1fdfa8 : mword 21, Regidx (mword_of_int 1))) bpdb_fa9fd0ef. Qed.

  Lemma bpi_2a : kernel_text -∗ instr (mword_of_int (BP + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BP + 0x2a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (BP + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma bpi_2c : kernel_text -∗ instr (mword_of_int (BP + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BP + 0x2c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (BP + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma bpi_2e : kernel_text -∗ instr (mword_of_int (BP + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BP + 0x2e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (BP + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma bpi_30 : kernel_text -∗ instr (mword_of_int (BP + 0x30) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BP + 0x30)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (BP + 0x30) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma bpi_32 : kernel_text -∗ instr (mword_of_int (BP + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BP + 0x32)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BP + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ---- bunpin ---- *)

  Lemma bui_00 : kernel_text -∗ instr (mword_of_int (BU + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (BU + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (BU + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma bui_02 : kernel_text -∗ instr (mword_of_int (BU + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (BU + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (BU + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma bui_04 : kernel_text -∗ instr (mword_of_int (BU + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (BU + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (BU + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma bui_06 : kernel_text -∗ instr (mword_of_int (BU + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (BU + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (BU + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma bui_08 : kernel_text -∗ instr (mword_of_int (BU + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (BU + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (BU + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma bui_0a : kernel_text -∗ instr (mword_of_int (BU + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (BU + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (BU + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma bui_0c : kernel_text -∗ instr (mword_of_int (BU + 0x0c) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BU + 0x0c)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BU + 0x0c) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bui_10 : kernel_text -∗ instr (mword_of_int (BU + 0x10) : mword 64) false (ITYPE (mword_of_int 0x48e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BU + 0x10)%Z (mword_of_int 0x48e50513 : mword 32)
    (mword_of_int (BU + 0x10) : mword 64) (ITYPE (mword_of_int 0x48e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bpdb_48e50513. Qed.

  Lemma bui_14 : kernel_text -∗ instr (mword_of_int (BU + 0x14) : mword 64) false (JAL (mword_of_int 0x1fdefe : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BU + 0x14)%Z (mword_of_int 0xefffd0ef : mword 32)
    (mword_of_int (BU + 0x14) : mword 64) (JAL (mword_of_int 0x1fdefe : mword 21, Regidx (mword_of_int 1))) bpdb_efffd0ef. Qed.

  Lemma bui_18 : kernel_text -∗ instr (mword_of_int (BU + 0x18) : mword 64) true (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (BU + 0x18)%Z (mword_of_int 0x40bc : mword 16)
    (mword_of_int (BU + 0x18) : mword 64) (LOAD (mword_of_int 64, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40bc cexec_40bc. Qed.

  Lemma bui_1a : kernel_text -∗ instr (mword_of_int (BU + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (BU + 0x1a)%Z (mword_of_int 0x37fd : mword 16)
    (mword_of_int (BU + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_37fd exec_execute_C_ADDIW. Qed.

  Lemma bui_1c : kernel_text -∗ instr (mword_of_int (BU + 0x1c) : mword 64) true (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (BU + 0x1c)%Z (mword_of_int 0xc0bc : mword 16)
    (mword_of_int (BU + 0x1c) : mword 64) (STORE (mword_of_int 64, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0bc cexec_c0bc. Qed.

  Lemma bui_1e : kernel_text -∗ instr (mword_of_int (BU + 0x1e) : mword 64) false (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (BU + 0x1e)%Z (mword_of_int 0x00015517 : mword 32)
    (mword_of_int (BU + 0x1e) : mword 64) (UTYPE (mword_of_int 0x15 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00015517. Qed.

  Lemma bui_22 : kernel_text -∗ instr (mword_of_int (BU + 0x22) : mword 64) false (ITYPE (mword_of_int 0x47c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (BU + 0x22)%Z (mword_of_int 0x47c50513 : mword 32)
    (mword_of_int (BU + 0x22) : mword 64) (ITYPE (mword_of_int 0x47c : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) bpdb_47c50513. Qed.

  Lemma bui_26 : kernel_text -∗ instr (mword_of_int (BU + 0x26) : mword 64) false (JAL (mword_of_int 0x1fdf74 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (BU + 0x26)%Z (mword_of_int 0xf75fd0ef : mword 32)
    (mword_of_int (BU + 0x26) : mword 64) (JAL (mword_of_int 0x1fdf74 : mword 21, Regidx (mword_of_int 1))) bpdb_f75fd0ef. Qed.

  Lemma bui_2a : kernel_text -∗ instr (mword_of_int (BU + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (BU + 0x2a)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (BU + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma bui_2c : kernel_text -∗ instr (mword_of_int (BU + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (BU + 0x2c)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (BU + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma bui_2e : kernel_text -∗ instr (mword_of_int (BU + 0x2e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (BU + 0x2e)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (BU + 0x2e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma bui_30 : kernel_text -∗ instr (mword_of_int (BU + 0x30) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (BU + 0x30)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (BU + 0x30) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma bui_32 : kernel_text -∗ instr (mword_of_int (BU + 0x32) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (BU + 0x32)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (BU + 0x32) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End BpinInstrs.

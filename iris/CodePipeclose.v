(* CodePipeclose.v -- the instruction-DECODE layer for xv6's pipeclose().
   For EVERY instruction of

     pipeclose @ 0x80004440 .. 0x8000449c   (offsets 0x00 .. 0x5c, 33 in all)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([pci_<off>]) plus
   the per-instruction decode facts they consume.  Same shape as
   CodePipealloc / CodeKalloc: [mk_rvc] for compressed instructions,
   [mk_base] for 4-byte ones.  Everything the rest of the tree already decodes
   comes from KernelRvcDecode as [cdec_<word>]; only the four words nothing
   else uses are local.

   Body (all instruction bytes from the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/pipe.c):

     0x00 1101       c.addi16sp is NOT used -- c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 e04a       c.sdsp s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32
     0x0c 84aa       c.mv   s1,a0            # s1 := pi
     0x0e 892e       c.mv   s2,a1            # s2 := writable
     0x10 fb8fc0ef   jal    ra,acquire
     0x14 02090763   beq    s2,zero,+0x2e    # -> 0x42, the readopen arm
     0x18 2204a223   sw     zero,548(s1)     # pi->writeopen = 0
     0x1c 21848513   addi   a0,s1,536        # a0 := &pi->nread
     0x20 af3fd0ef   jal    ra,wakeup
     0x24 2204a783   lw     a5,544(s1)       # a5 := pi->readopen
     0x28 e781       c.bnez a5,+0x8          # -> 0x30, still open: plain release
     0x2a 2244a783   lw     a5,548(s1)       # a5 := pi->writeopen
     0x2e c38d       c.beqz a5,+0x22         # -> 0x50, BOTH shut: free the page
     0x30 8526       c.mv   a0,s1
     0x32 81ffc0ef   jal    ra,release
     0x36 60e2 / 0x38 6442 / 0x3a 64a2 / 0x3c 6902 / 0x3e 6105 / 0x40 8082
                                             # the epilogue
     0x42 2204a023   sw     zero,544(s1)     # pi->readopen = 0
     0x46 21c48513   addi   a0,s1,540        # a0 := &pi->nwrite
     0x4a ac9fd0ef   jal    ra,wakeup
     0x4e bfd9       c.j    -0x2a            # -> 0x24, join
     0x50 8526       c.mv   a0,s1
     0x52 ffefc0ef   jal    ra,release
     0x56 8526       c.mv   a0,s1
     0x58 daefc0ef   jal    ra,kfree
     0x5c bfe9       c.j    -0x26            # -> 0x36, join with the epilogue

   Note the two arms of [if (writable)] are NOT symmetric in the binary: the
   writable arm falls through and the other is out of line, and they rejoin at
   0x24 -- so the flag test at 0x24/0x2a reads BOTH words in both arms.       *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
Require Import WpDecodeBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

Notation PC := KernelSyms.pipeclose.

(* ===================================================================== *)
(* Compressed decode facts nothing else in the tree needs.                *)
(* ===================================================================== *)

(* 0xe781  c.bnez a5,+0x8 *)
Lemma pcdc_e781 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe781 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 4, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.



(* ===================================================================== *)
(* 4-byte decode facts.                                                   *)
(* ===================================================================== *)

Local Ltac pc_ast :=
  first [ reflexivity
        | repeat f_equal;
          first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ].

Local Ltac pc_dbase s Hpriv :=
  decode_pause_prefix s Hpriv;
  match goal with |- ?lhs = ?rhs =>
    let l := eval vm_compute in lhs in change_no_check (l = rhs) end;
  pc_ast.

(* +0x10  0xfb8fc0ef  jal ra,acquire *)
Lemma pcdb_acquire s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfb8fc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082744 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* +0x14  0x02090763  beq s2,zero,+0x2e *)
Lemma pcdb_beq s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02090763 : mword 32)) s
  = Some (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BEQ), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* +0x18  0x2204a223  sw zero,548(s1) *)
Lemma pcdb_sw_wo s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2204a223 : mword 32)) s
  = Some (STORE (mword_of_int 548, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.


(* +0x20  0xaf3fd0ef  jal ra,wakeup *)
Lemma pcdb_wakeup1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xaf3fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087666 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.



(* +0x32  0x81ffc0ef  jal ra,release *)
Lemma pcdb_release1 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81ffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082846 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* +0x42  0x2204a023  sw zero,544(s1) *)
Lemma pcdb_sw_ro s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x2204a023 : mword 32)) s
  = Some (STORE (mword_of_int 544, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.


(* +0x4a  0xac9fd0ef  jal ra,wakeup *)
Lemma pcdb_wakeup2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xac9fd0ef : mword 32)) s
  = Some (JAL (mword_of_int 2087624 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* +0x52  0xffefc0ef  jal ra,release *)
Lemma pcdb_release2 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xffefc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082814 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* +0x58  0xdaefc0ef  jal ra,kfree *)
Lemma pcdb_kfree s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdaefc0ef : mword 32)) s
  = Some (JAL (mword_of_int 2082222 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; pc_dbase s Hpriv ]. Qed.

(* ===================================================================== *)
(* [instr] facts.                                                         *)
(* ===================================================================== *)
Section WpPipecloseInstr.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma pci_00 : kernel_text -∗ instr (mword_of_int (PC + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (PC + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (PC + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma pci_02 : kernel_text -∗ instr (mword_of_int (PC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (PC + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (PC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma pci_04 : kernel_text -∗ instr (mword_of_int (PC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (PC + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (PC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma pci_06 : kernel_text -∗ instr (mword_of_int (PC + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (PC + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (PC + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma pci_08 : kernel_text -∗ instr (mword_of_int (PC + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (PC + 0x08)%Z (mword_of_int 0xe04a : mword 16)
    (mword_of_int (PC + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma pci_0a : kernel_text -∗ instr (mword_of_int (PC + 0x0a) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (PC + 0x0a)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (PC + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma pci_0c : kernel_text -∗ instr (mword_of_int (PC + 0x0c) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (PC + 0x0c)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (PC + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma pci_0e : kernel_text -∗ instr (mword_of_int (PC + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (PC + 0x0e)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (PC + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma pci_10 : kernel_text -∗ instr (mword_of_int (PC + 0x10) : mword 64) false (JAL (mword_of_int 2082744 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x10)%Z (mword_of_int 0xfb8fc0ef : mword 32)
    (mword_of_int (PC + 0x10) : mword 64) (JAL (mword_of_int 2082744 : mword 21, Regidx (mword_of_int 1))) pcdb_acquire. Qed.

  Lemma pci_14 : kernel_text -∗ instr (mword_of_int (PC + 0x14) : mword 64) false (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BEQ)).
  Proof. mk_base (PC + 0x14)%Z (mword_of_int 0x02090763 : mword 32)
    (mword_of_int (PC + 0x14) : mword 64) (BTYPE (mword_of_int 46 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 18), BEQ)) pcdb_beq. Qed.

  Lemma pci_18 : kernel_text -∗ instr (mword_of_int (PC + 0x18) : mword 64) false (STORE (mword_of_int 548, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (PC + 0x18)%Z (mword_of_int 0x2204a223 : mword 32)
    (mword_of_int (PC + 0x18) : mword 64) (STORE (mword_of_int 548, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) pcdb_sw_wo. Qed.

  Lemma pci_1c : kernel_text -∗ instr (mword_of_int (PC + 0x1c) : mword 64) false (ITYPE (mword_of_int 536, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PC + 0x1c)%Z (mword_of_int 0x21848513 : mword 32)
    (mword_of_int (PC + 0x1c) : mword 64) (ITYPE (mword_of_int 536, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_21848513. Qed.

  Lemma pci_20 : kernel_text -∗ instr (mword_of_int (PC + 0x20) : mword 64) false (JAL (mword_of_int 2087666 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x20)%Z (mword_of_int 0xaf3fd0ef : mword 32)
    (mword_of_int (PC + 0x20) : mword 64) (JAL (mword_of_int 2087666 : mword 21, Regidx (mword_of_int 1))) pcdb_wakeup1. Qed.

  Lemma pci_24 : kernel_text -∗ instr (mword_of_int (PC + 0x24) : mword 64) false (LOAD (mword_of_int 544, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PC + 0x24)%Z (mword_of_int 0x2204a783 : mword 32)
    (mword_of_int (PC + 0x24) : mword 64) (LOAD (mword_of_int 544, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2204a783. Qed.

  Lemma pci_28 : kernel_text -∗ instr (mword_of_int (PC + 0x28) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (PC + 0x28)%Z (mword_of_int 0xe781 : mword 16)
    (mword_of_int (PC + 0x28) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 4 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) pcdc_e781 exec_execute_C_BNEZ. Qed.

  Lemma pci_2a : kernel_text -∗ instr (mword_of_int (PC + 0x2a) : mword 64) false (LOAD (mword_of_int 548, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_base (PC + 0x2a)%Z (mword_of_int 0x2244a783 : mword 32)
    (mword_of_int (PC + 0x2a) : mword 64) (LOAD (mword_of_int 548, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) bdec_2244a783. Qed.

  Lemma pci_2e : kernel_text -∗ instr (mword_of_int (PC + 0x2e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (PC + 0x2e)%Z (mword_of_int 0xc38d : mword 16)
    (mword_of_int (PC + 0x2e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) cdec_c38d exec_execute_C_BEQZ. Qed.

  Lemma pci_30 : kernel_text -∗ instr (mword_of_int (PC + 0x30) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PC + 0x30)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PC + 0x30) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pci_32 : kernel_text -∗ instr (mword_of_int (PC + 0x32) : mword 64) false (JAL (mword_of_int 2082846 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x32)%Z (mword_of_int 0x81ffc0ef : mword 32)
    (mword_of_int (PC + 0x32) : mword 64) (JAL (mword_of_int 2082846 : mword 21, Regidx (mword_of_int 1))) pcdb_release1. Qed.

  Lemma pci_36 : kernel_text -∗ instr (mword_of_int (PC + 0x36) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (PC + 0x36)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (PC + 0x36) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma pci_38 : kernel_text -∗ instr (mword_of_int (PC + 0x38) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (PC + 0x38)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (PC + 0x38) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma pci_3a : kernel_text -∗ instr (mword_of_int (PC + 0x3a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (PC + 0x3a)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (PC + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma pci_3c : kernel_text -∗ instr (mword_of_int (PC + 0x3c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (PC + 0x3c)%Z (mword_of_int 0x6902 : mword 16)
    (mword_of_int (PC + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma pci_3e : kernel_text -∗ instr (mword_of_int (PC + 0x3e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (PC + 0x3e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (PC + 0x3e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma pci_40 : kernel_text -∗ instr (mword_of_int (PC + 0x40) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (PC + 0x40)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (PC + 0x40) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  Lemma pci_42 : kernel_text -∗ instr (mword_of_int (PC + 0x42) : mword 64) false (STORE (mword_of_int 544, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (PC + 0x42)%Z (mword_of_int 0x2204a023 : mword 32)
    (mword_of_int (PC + 0x42) : mword 64) (STORE (mword_of_int 544, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 4)) pcdb_sw_ro. Qed.

  Lemma pci_46 : kernel_text -∗ instr (mword_of_int (PC + 0x46) : mword 64) false (ITYPE (mword_of_int 540, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (PC + 0x46)%Z (mword_of_int 0x21c48513 : mword 32)
    (mword_of_int (PC + 0x46) : mword 64) (ITYPE (mword_of_int 540, Regidx (mword_of_int 9), Regidx (mword_of_int 10), ADDI)) bdec_21c48513. Qed.

  Lemma pci_4a : kernel_text -∗ instr (mword_of_int (PC + 0x4a) : mword 64) false (JAL (mword_of_int 2087624 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x4a)%Z (mword_of_int 0xac9fd0ef : mword 32)
    (mword_of_int (PC + 0x4a) : mword 64) (JAL (mword_of_int 2087624 : mword 21, Regidx (mword_of_int 1))) pcdb_wakeup2. Qed.

  Lemma pci_4e : kernel_text -∗ instr (mword_of_int (PC + 0x4e) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PC + 0x4e)%Z (mword_of_int 0xbfd9 : mword 16)
    (mword_of_int (PC + 0x4e) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2027 : mword 11) ('b"0")), zreg)) cdec_bfd9 exec_execute_C_J. Qed.

  Lemma pci_50 : kernel_text -∗ instr (mword_of_int (PC + 0x50) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PC + 0x50)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PC + 0x50) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pci_52 : kernel_text -∗ instr (mword_of_int (PC + 0x52) : mword 64) false (JAL (mword_of_int 2082814 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x52)%Z (mword_of_int 0xffefc0ef : mword 32)
    (mword_of_int (PC + 0x52) : mword 64) (JAL (mword_of_int 2082814 : mword 21, Regidx (mword_of_int 1))) pcdb_release2. Qed.

  Lemma pci_56 : kernel_text -∗ instr (mword_of_int (PC + 0x56) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (PC + 0x56)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (PC + 0x56) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pci_58 : kernel_text -∗ instr (mword_of_int (PC + 0x58) : mword 64) false (JAL (mword_of_int 2082222 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (PC + 0x58)%Z (mword_of_int 0xdaefc0ef : mword 32)
    (mword_of_int (PC + 0x58) : mword 64) (JAL (mword_of_int 2082222 : mword 21, Regidx (mword_of_int 1))) pcdb_kfree. Qed.

  Lemma pci_5c : kernel_text -∗ instr (mword_of_int (PC + 0x5c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (PC + 0x5c)%Z (mword_of_int 0xbfe9 : mword 16)
    (mword_of_int (PC + 0x5c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2029 : mword 11) ('b"0")), zreg)) cdec_bfe9 exec_execute_C_J. Qed.

End WpPipecloseInstr.

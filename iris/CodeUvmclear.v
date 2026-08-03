(* CodeUvmclear.v -- the instruction-DECODE layer for xv6's uvmclear().

     uvmclear @ 0x8000149e .. 0x800014c7   (offsets 0x00 .. 0x26, 17 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([ucli_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the four 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>] / KernelBaseDecode as [bdec_<word>]; uvmclear's own words are
   local, named [ucldc_<word>] (compressed) / [ucldb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/vm.c's

     void uvmclear(pagetable_t pagetable, uint64 va)   // a0, a1
     { pte_t *pte = walk(pagetable, va, 0);
       if (pte == 0) panic("uvmclear");
       *pte &= ~PTE_U; }                                                 ):

     0x00 1141       c.addi sp,sp,-16       # 16-byte frame, 2 slots
     0x02 e406       c.sdsp ra,8(sp)
     0x04 e022       c.sdsp s0,0(sp)
     0x06 0800       c.addi4spn s0,sp,16
     0x08 4601       c.li   a2,0            # alloc = 0
     0x0a ab5ff0ef   jal    ra,walk         # 0x80000f5c
     0x0e c901       c.beqz a0,+0x10        # -> 0x1e, the panic block (DEAD)
     0x10 611c       c.ld   a5,0(a0)        # a5 = *pte
     0x12 9bbd       c.andi a5,a5,-17       # a5 &= ~PTE_U
     0x14 e11c       c.sd   a5,0(a0)        # *pte = a5
     0x16 60a2       c.ldsp ra,8(sp)
     0x18 6402       c.ldsp s0,0(sp)
     0x1a 0141       c.addi sp,sp,16
     0x1c 8082       c.ret
     0x1e 00006517   auipc  a0,0x6          # --- the panic block
     0x22 c8c50513   addi   a0,a0,-884      # the "uvmclear" message @ 0x80007148
     0x26 b62ff0ef   jal    ra,panic        # 0x80000826

   THE FRAME PAIR IS *NOT* THE TWO-AST IDIOM.  uvmdealloc / uvmfree / freewalk
   each trade a frame in with one AST and back out with another, because the
   POSITIVE displacement does not fit the 6-bit signed C.ADDI immediate and
   gcc has to reach for [c.addi16sp].  Here the frame is only 16 bytes, so
   BOTH ends fit (-16 -> residue 48, +16 -> 16) and both words are plain
   [C_ADDI] on sp: 0x1141 at 0x00 and 0x0141 at 0x1a decode to the SAME
   [ITYPE (sign_extend' 12 _, csp_rs1, csp_rs1, ADDI)] shape, differing only
   in the immediate.  (0x0141 is funct3 = 000 / op = 01 with rd = x2; the
   [c.addi16sp] encoding of +16 would be 0x6141, funct3 = 011.  objdump
   prints both as "addi sp,sp,16", which is what invites the mistake.)

   THE NEGATIVE c.andi.  0x9bbd is [c.andi a5,a5,-17]: the C.ANDI immediate is
   a 6-bit SIGNED field, -17 is in range (-32..31), and its 6-bit residue is
   47.  [exec_execute_C_ANDI] keeps that immediate symbolic and only bridges
   the creg, so the AST carries it as [sign_extend' 12 (mword_of_int 47 :
   mword 6)] -- the decoder's POSITIVE residue, exactly as for the negative
   [c.addi sp,sp,-16] above (48, not -16).

   THE MEMORY PAIR AT 0x10 / 0x14 is stated in the leaf-friendly shape (a
   literal [mword 12] displacement and plain [Regidx]es) rather than the
   decoder's [zero_extend' 12 (concat_vec _ 'b"000")] / [creg2reg_idx] form,
   since that is what the WP load/store leaves take: [cexec_611c] is the
   shared bridge for the load, [ucexec_e11c] its local store twin.

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2 residue
   for C_J / C_BEQZ / C_BNEZ:

     0x0a ab5ff0ef  JAL    arg(mword 21) = 2095796   (2^21 - 1356, walk)
     0x0e c901      C_BEQZ arg(mword 8)  = 8         (+0x10 -> 0x1e)
     0x26 b62ff0ef  JAL    arg(mword 21) = 2093922   (2^21 - 3230, panic)   *)
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
Require Import KernelRvcDecode KernelBaseDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for uvmclear's own words.                      *)
(* ===================================================================== *)

(* Reused verbatim from the shared catalog (KernelRvcDecode.v):

     0x00  c.addi sp,sp,-16    [cdec_1141]
     0x02  c.sdsp ra,8(sp)     [cdec_e406]
     0x04  c.sdsp s0,0(sp)     [cdec_e022]
     0x06  c.addi4spn s0,sp,16 [cdec_0800]
     0x08  c.li   a2,0         [cdec_4601]
     0x10  c.ld   a5,0(a0)     [cdec_611c] + its leaf shape [cexec_611c]
     0x16  c.ldsp ra,8(sp)     [cdec_60a2]
     0x18  c.ldsp s0,0(sp)     [cdec_6402]
     0x1a  c.addi sp,sp,16     [cdec_0141]
     0x1c  c.ret               [cdec_8082]                               *)


(* 0x12  c.andi a5,a5,-17  (creg 7 = a5; 6-bit residue of -17 is 47) *)
Lemma ucldc_9bbd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9bbd : mword 16)) s
  = Some (C_ANDI (mword_of_int 47, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* [cdec_e11c]'s AST in the shape a WP store leaf takes -- the twin of the
   shared [cexec_611c] the load at 0x10 uses. *)
Lemma ucexec_e11c s :
  exec (execute (C_SD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 7)))) s
  = Some (ExecuteAs (STORE (mword_of_int 0, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 8)), s).
Proof. apply exec_execute_C_SD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0x1e  auipc a0,0x6 *)
(* [bdec_00006517] -- shared, see KernelBaseDecode.v *)

(* 0x0a  jal ra,walk  (0x800014a8 -> 0x80000f5c is -0x54c = -1356) *)
Lemma ucldb_ab5ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xab5ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095796 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x22  addi a0,a0,-884  -- the "uvmclear" message (12-bit residue 3212) *)
Lemma ucldb_c8c50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc8c50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  jal ra,panic  (0x800014c4 -> 0x80000826 is -0xc9e = -3230) *)
Lemma ucldb_b62ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xb62ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2093922 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmclearInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation UC := KernelSyms.uvmclear.

  (* --- prologue: a 2-slot frame saving ra/s0 -------------------------- *)

  Lemma ucli_00 : kernel_text -∗ instr (mword_of_int (UC + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UC + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (UC + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma ucli_02 : kernel_text -∗ instr (mword_of_int (UC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UC + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (UC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma ucli_04 : kernel_text -∗ instr (mword_of_int (UC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UC + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (UC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma ucli_06 : kernel_text -∗ instr (mword_of_int (UC + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UC + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (UC + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* --- pte = walk(pagetable, va, 0) ----------------------------------- *)

  Lemma ucli_08 : kernel_text -∗ instr (mword_of_int (UC + 0x08) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (UC + 0x08)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (UC + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma ucli_0a : kernel_text -∗ instr (mword_of_int (UC + 0x0a) : mword 64) false (JAL (mword_of_int 2095796 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x0a)%Z (mword_of_int 0xab5ff0ef : mword 32)
    (mword_of_int (UC + 0x0a) : mword 64) (JAL (mword_of_int 2095796 : mword 21, Regidx (mword_of_int 1))) ucldb_ab5ff0ef. Qed.

  Lemma ucli_0e : kernel_text -∗ instr (mword_of_int (UC + 0x0e) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (UC + 0x0e)%Z (mword_of_int 0xc901 : mword 16)
    (mword_of_int (UC + 0x0e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 8 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c901 exec_execute_C_BEQZ. Qed.

  (* --- *pte &= ~PTE_U ------------------------------------------------- *)

  Lemma ucli_10 : kernel_text -∗ instr (mword_of_int (UC + 0x10) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)).
  Proof. mk_rvc (UC + 0x10)%Z (mword_of_int 0x611c : mword 16)
    (mword_of_int (UC + 0x10) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 15), false, 8)) cdec_611c cexec_611c. Qed.

  Lemma ucli_12 : kernel_text -∗ instr (mword_of_int (UC + 0x12) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 47 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)).
  Proof. mk_rvc (UC + 0x12)%Z (mword_of_int 0x9bbd : mword 16)
    (mword_of_int (UC + 0x12) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 47 : mword 6), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), ANDI)) ucldc_9bbd exec_execute_C_ANDI. Qed.

  Lemma ucli_14 : kernel_text -∗ instr (mword_of_int (UC + 0x14) : mword 64) true (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 8)).
  Proof. mk_rvc (UC + 0x14)%Z (mword_of_int 0xe11c : mword 16)
    (mword_of_int (UC + 0x14) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 10), 8)) cdec_e11c ucexec_e11c. Qed.

  (* --- epilogue ------------------------------------------------------- *)

  Lemma ucli_16 : kernel_text -∗ instr (mword_of_int (UC + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UC + 0x16)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (UC + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma ucli_18 : kernel_text -∗ instr (mword_of_int (UC + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UC + 0x18)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (UC + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma ucli_1a : kernel_text -∗ instr (mword_of_int (UC + 0x1a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UC + 0x1a)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (UC + 0x1a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma ucli_1c : kernel_text -∗ instr (mword_of_int (UC + 0x1c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UC + 0x1c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UC + 0x1c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the panic block: pte == 0 (DEAD -- the vpn is mapped) ----------- *)

  Lemma ucli_1e : kernel_text -∗ instr (mword_of_int (UC + 0x1e) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UC + 0x1e)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (UC + 0x1e) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma ucli_22 : kernel_text -∗ instr (mword_of_int (UC + 0x22) : mword 64) false (ITYPE (mword_of_int 3212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UC + 0x22)%Z (mword_of_int 0xc8c50513 : mword 32)
    (mword_of_int (UC + 0x22) : mword 64) (ITYPE (mword_of_int 3212 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) ucldb_c8c50513. Qed.

  Lemma ucli_26 : kernel_text -∗ instr (mword_of_int (UC + 0x26) : mword 64) false (JAL (mword_of_int 2093922 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UC + 0x26)%Z (mword_of_int 0xb62ff0ef : mword 32)
    (mword_of_int (UC + 0x26) : mword 64) (JAL (mword_of_int 2093922 : mword 21, Regidx (mword_of_int 1))) ucldb_b62ff0ef. Qed.

End UvmclearInstrs.

(* CodeUvmfree.v -- the instruction-DECODE layer for xv6's uvmfree().

     uvmfree @ 0x800013d2 .. 0x80001403   (offsets 0x00 .. 0x30, 22 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([ufi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the three 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; uvmfree's own words are local, named [ufdc_<word>]
   (compressed) / [ufdb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/vm.c's
   [void uvmfree(pagetable_t pagetable, uint64 sz)], a0 = pagetable,
   a1 = sz):

     0x00 1101       c.addi sp,sp,-32       # 32-byte frame (4 slots)
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84aa       c.mv   s1,a0           # s1 := pagetable (survives the call)
     0x0c e989       c.bnez a1,+0x12        # -> 0x1e, sz > 0: unmap first
     0x0e 8526       c.mv   a0,s1           # --- the tail: freewalk(pagetable)
     0x10 f95ff0ef   jal    ra,freewalk     # 0x80001376
     0x14 60e2       c.ldsp ra,24(sp)
     0x16 6442       c.ldsp s0,16(sp)
     0x18 64a2       c.ldsp s1,8(sp)
     0x1a 6105       c.addi16sp sp,32
     0x1c 8082       c.ret
     0x1e 6785       c.lui  a5,0x1          # --- the unmap arm
     0x20 17fd       c.addi a5,a5,-1        # a5 := 0xfff
     0x22 95be       c.add  a1,a1,a5        # a1 := sz + 0xfff
     0x24 4685       c.li   a3,1            # do_free = 1
     0x26 00c5d613   srli   a2,a1,0xc       # npages = PGROUNDUP(sz)/PGSIZE
     0x2a 4581       c.li   a1,0            # va = 0
     0x2c e01ff0ef   jal    ra,uvmunmap     # 0x800011fe
     0x30 bff9       c.j    -0x22           # -> 0x0e, join the tail

   Note the two frame-pointer idioms for the SAME 32-byte frame: the prologue's
   0x1101 is a plain [c.addi sp,sp,-32] (-32 fits the 6-bit signed C.ADDI
   immediate), while the epilogue's 0x6105 is a [c.addi16sp sp,32] (+32 does
   not), so the two decode to different ASTs -- [C_ADDI] vs [C_ADDI16SP].
   uvmdealloc's prologue/epilogue pair is the same idiom (CodeUvmdealloc.v).

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2 residue
   for C_J / C_BNEZ:

     0x0c e989      C_BNEZ arg(mword 8)  = 9         (+0x12 -> 0x1e)
     0x10 f95ff0ef  JAL    arg(mword 21) = 2097044   (2^21 - 108, freewalk)
     0x2c e01ff0ef  JAL    arg(mword 21) = 2096640   (2^21 - 512, uvmunmap)
     0x30 bff9      C_J    arg(mword 11) = 2031      (2^11 - 17, -0x22)      *)
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
(* Compressed decode facts for uvmfree's own words.                       *)
(* ===================================================================== *)

(* Reused verbatim from the shared catalog (KernelRvcDecode.v):

     0x00  c.addi sp,sp,-32     [cdec_1101]
     0x02  c.sdsp ra,24(sp)     [cdec_ec06]
     0x04  c.sdsp s0,16(sp)     [cdec_e822]
     0x06  c.sdsp s1,8(sp)      [cdec_e426]
     0x08  c.addi4spn s0,sp,32  [cdec_1000]
     0x0a  c.mv   s1,a0         [cdec_84aa]
     0x0e  c.mv   a0,s1         [cdec_8526]
     0x14  c.ldsp ra,24(sp)     [cdec_60e2]
     0x16  c.ldsp s0,16(sp)     [cdec_6442]
     0x18  c.ldsp s1,8(sp)      [cdec_64a2]
     0x1a  c.addi16sp sp,32     [cdec_6105]
     0x1c  c.ret                [cdec_8082]
     0x1e  c.lui  a5,0x1        [cdec_6785]
     0x20  c.addi a5,a5,-1      [cdec_17fd]
     0x22  c.add  a1,a1,a5      [cdec_95be]
     0x2a  c.li   a1,0          [cdec_4581]
     0x30  c.j    -0x22         [cdec_bff9]                              *)

(* 0x0c  c.bnez a1,+0x12  (creg 3 = a1; offset/2 = 9) *)
Lemma ufdc_e989 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe989 : mword 16)) s
  = Some (C_BNEZ (mword_of_int 9, Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* ===================================================================== *)
(* Base (4-byte) decode facts -- all three are uvmfree's own.             *)
(* ===================================================================== *)

(* 0x10  jal ra,freewalk  (0x800013e2 -> 0x80001376 is -0x6c = -108) *)
Lemma ufdb_f95ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf95ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2097044 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  srli a2,a1,0xc  -- npages = PGROUNDUP(sz) / PGSIZE *)
Lemma ufdb_00c5d613 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00c5d613 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11),
                    Regidx (mword_of_int 12), SRLI), s).
Proof. decode_bridge_ms. Qed.

(* 0x2c  jal ra,uvmunmap  (0x800013fe -> 0x800011fe is -0x200 = -512) *)
Lemma ufdb_e01ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe01ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096640 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmfreeInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation UF := KernelSyms.uvmfree.

  (* --- prologue: 32-byte frame saving ra/s0/s1 ------------------------ *)

  Lemma ufi_00 : kernel_text -∗ instr (mword_of_int (UF + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (UF + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (UF + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma ufi_02 : kernel_text -∗ instr (mword_of_int (UF + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UF + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (UF + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma ufi_04 : kernel_text -∗ instr (mword_of_int (UF + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UF + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (UF + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma ufi_06 : kernel_text -∗ instr (mword_of_int (UF + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UF + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (UF + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma ufi_08 : kernel_text -∗ instr (mword_of_int (UF + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UF + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (UF + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- s1 := pagetable, then the [sz > 0] test ------------------------ *)

  Lemma ufi_0a : kernel_text -∗ instr (mword_of_int (UF + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UF + 0x0a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (UF + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma ufi_0c : kernel_text -∗ instr (mword_of_int (UF + 0x0c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)).
  Proof. mk_rvc (UF + 0x0c)%Z (mword_of_int 0xe989 : mword 16)
    (mword_of_int (UF + 0x0c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 9 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 3)), BNE)) ufdc_e989 exec_execute_C_BNEZ. Qed.

  (* --- the tail: freewalk(pagetable) and the epilogue ------------------ *)

  Lemma ufi_0e : kernel_text -∗ instr (mword_of_int (UF + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UF + 0x0e)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (UF + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma ufi_10 : kernel_text -∗ instr (mword_of_int (UF + 0x10) : mword 64) false (JAL (mword_of_int 2097044 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UF + 0x10)%Z (mword_of_int 0xf95ff0ef : mword 32)
    (mword_of_int (UF + 0x10) : mword 64) (JAL (mword_of_int 2097044 : mword 21, Regidx (mword_of_int 1))) ufdb_f95ff0ef. Qed.

  Lemma ufi_14 : kernel_text -∗ instr (mword_of_int (UF + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UF + 0x14)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (UF + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma ufi_16 : kernel_text -∗ instr (mword_of_int (UF + 0x16) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UF + 0x16)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (UF + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma ufi_18 : kernel_text -∗ instr (mword_of_int (UF + 0x18) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UF + 0x18)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (UF + 0x18) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma ufi_1a : kernel_text -∗ instr (mword_of_int (UF + 0x1a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UF + 0x1a)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (UF + 0x1a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma ufi_1c : kernel_text -∗ instr (mword_of_int (UF + 0x1c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UF + 0x1c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UF + 0x1c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the unmap arm: PGROUNDUP(sz)/PGSIZE pages from va = 0 ---------- *)

  Lemma ufi_1e : kernel_text -∗ instr (mword_of_int (UF + 0x1e) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (UF + 0x1e)%Z (mword_of_int 0x6785 : mword 16)
    (mword_of_int (UF + 0x1e) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)) cdec_6785 exec_execute_C_LUI. Qed.

  Lemma ufi_20 : kernel_text -∗ instr (mword_of_int (UF + 0x20) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (UF + 0x20)%Z (mword_of_int 0x17fd : mword 16)
    (mword_of_int (UF + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cdec_17fd exec_execute_C_ADDI. Qed.

  Lemma ufi_22 : kernel_text -∗ instr (mword_of_int (UF + 0x22) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (UF + 0x22)%Z (mword_of_int 0x95be : mword 16)
    (mword_of_int (UF + 0x22) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADD)) cdec_95be exec_execute_C_ADD. Qed.

  Lemma ufi_24 : kernel_text -∗ instr (mword_of_int (UF + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (UF + 0x24)%Z (mword_of_int 0x4685 : mword 16)
    (mword_of_int (UF + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4685 exec_execute_C_LI. Qed.

  Lemma ufi_26 : kernel_text -∗ instr (mword_of_int (UF + 0x26) : mword 64) false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 12), SRLI)).
  Proof. mk_base (UF + 0x26)%Z (mword_of_int 0x00c5d613 : mword 32)
    (mword_of_int (UF + 0x26) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 12), SRLI)) ufdb_00c5d613. Qed.

  Lemma ufi_2a : kernel_text -∗ instr (mword_of_int (UF + 0x2a) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)).
  Proof. mk_rvc (UF + 0x2a)%Z (mword_of_int 0x4581 : mword 16)
    (mword_of_int (UF + 0x2a) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 11), ADDI)) cdec_4581 exec_execute_C_LI. Qed.

  Lemma ufi_2c : kernel_text -∗ instr (mword_of_int (UF + 0x2c) : mword 64) false (JAL (mword_of_int 2096640 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UF + 0x2c)%Z (mword_of_int 0xe01ff0ef : mword 32)
    (mword_of_int (UF + 0x2c) : mword 64) (JAL (mword_of_int 2096640 : mword 21, Regidx (mword_of_int 1))) ufdb_e01ff0ef. Qed.

  Lemma ufi_30 : kernel_text -∗ instr (mword_of_int (UF + 0x30) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UF + 0x30)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (UF + 0x30) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

End UvmfreeInstrs.

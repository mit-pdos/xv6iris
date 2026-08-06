(* CodeUvmdealloc.v -- the instruction-DECODE layer for xv6's uvmdealloc().

     uvmdealloc @ 0x80001288 .. 0x800012cb   (offsets 0x00 .. 0x42, 29 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([udi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the five 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; uvmdealloc's own words are local, named [uddc_<word>]
   (compressed) / [uddb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/vm.c's
   [uint64 uvmdealloc(pagetable_t pagetable, uint64 oldsz, uint64 newsz)],
   a0 = pagetable, a1 = oldsz, a2 = newsz):

     0x00 1101       c.addi sp,sp,-32       # 32-byte frame (4 slots)
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 84ae       c.mv   s1,a1           # s1 := oldsz  (the return value)
     0x0c 00b67d63   bgeu   a2,a1,+0x1a     # -> 0x26, newsz >= oldsz: done
     0x10 84b2       c.mv   s1,a2           # s1 := newsz
     0x12 6785       c.lui  a5,0x1
     0x14 17fd       c.addi a5,a5,-1        # a5 := 0xfff
     0x16 00f60733   add    a4,a2,a5
     0x1a 76fd       c.lui  a3,0xfffff      # a3 := -4096
     0x1c 8f75       c.and  a4,a4,a3        # a4 := PGROUNDUP(newsz)
     0x1e 97ae       c.add  a5,a5,a1
     0x20 8ff5       c.and  a5,a5,a3        # a5 := PGROUNDUP(oldsz)
     0x22 00f76863   bltu   a4,a5,+0x10     # -> 0x32, something to unmap
     0x26 8526       c.mv   a0,s1           # --- the epilogue, fed by 3 arms
     0x28 60e2       c.ldsp ra,24(sp)
     0x2a 6442       c.ldsp s0,16(sp)
     0x2c 64a2       c.ldsp s1,8(sp)
     0x2e 6105       c.addi sp,sp,32
     0x30 8082       c.ret
     0x32 8f99       c.sub  a5,a5,a4        # --- the unmap arm
     0x34 83b1       c.srli a5,a5,0xc       # npages
     0x36 4685       c.li   a3,1            # do_free = 1
     0x38 0007861b   sext.w a2,a5           # (ADDIW rd,rs1,0)
     0x3c 85ba       c.mv   a1,a4
     0x3e f39ff0ef   jal    ra,uvmunmap     # 0x800011fe
     0x42 b7d5       c.j    -0x1c           # -> 0x26

   Note the two frame-pointer idioms for the SAME 32-byte frame: the prologue's
   0x1101 is a plain [c.addi sp,sp,-32] (-32 fits the 6-bit signed C.ADDI
   immediate), while the epilogue's 0x6105 is a [c.addi16sp sp,32] (+32 does
   not), so the two decode to different ASTs -- [C_ADDI] vs [C_ADDI16SP].

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2 residue
   for C_J:

     0x0c 00b67d63  BTYPE arg(mword 13) = 26        -> 0x26
     0x22 00f76863  BTYPE arg(mword 13) = 16        -> 0x32
     0x3e f39ff0ef  JAL   arg(mword 21) = 2096952   (2^21 - 200, uvmunmap)
     0x42 b7d5      C_J   arg(mword 11) = 2034      (2^11 - 14, -0x1c)      *)
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

(* ===================================================================== *)
(* Compressed decode facts for uvmdealloc's own words.                    *)
(* ===================================================================== *)

(* 0x00  c.addi sp,sp,-32   -- [cdec_1101] (KernelRvcDecode.v) *)
(* 0x02  c.sdsp ra,24(sp)   -- [cdec_ec06] (KernelRvcDecode.v) *)
(* 0x04  c.sdsp s0,16(sp)   -- [cdec_e822] (KernelRvcDecode.v) *)
(* 0x06  c.sdsp s1,8(sp)    -- [cdec_e426] (KernelRvcDecode.v) *)
(* 0x08  c.addi4spn s0,sp,32 -- [cdec_1000] (KernelRvcDecode.v) *)
(* 0x26  c.mv a0,s1         -- [cdec_8526] (KernelRvcDecode.v) *)
(* 0x28  c.ldsp ra,24(sp)   -- [cdec_60e2] (KernelRvcDecode.v) *)
(* 0x2a  c.ldsp s0,16(sp)   -- [cdec_6442] (KernelRvcDecode.v) *)
(* 0x2c  c.ldsp s1,8(sp)    -- [cdec_64a2] (KernelRvcDecode.v) *)
(* 0x2e  c.addi16sp sp,32   -- [cdec_6105] (KernelRvcDecode.v) *)
(* 0x30  c.ret              -- [cdec_8082] (KernelRvcDecode.v) *)
(* 0x34  c.srli a5,a5,0xc   -- [cdec_83b1] (KernelRvcDecode.v) *)

(* 0x0a  c.mv s1,a1 *)
(* [cdec_84ae] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x10  c.mv s1,a2 *)
(* [cdec_84b2] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x12  c.lui a5,0x1 *)
(* [cdec_6785] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x14  c.addi a5,a5,-1  (imm6 = 63, the 6-bit residue of -1) *)
(* [cdec_17fd] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1a  c.lui a3,0xfffff  (imm6 = 63, the 6-bit residue of -1) *)
Lemma uddc_76fd s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x76fd : mword 16)) s
  = Some (C_LUI (mword_of_int 63, Regidx (mword_of_int 13)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x1e  c.add a5,a5,a1 *)
Lemma uddc_97ae s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x97ae : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 15), Regidx (mword_of_int 11)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x20  c.and a5,a5,a3  (creg 7 = a5, creg 5 = a3) *)
Lemma uddc_8ff5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8ff5 : mword 16)) s
  = Some (C_AND (Cregidx (mword_of_int 7), Cregidx (mword_of_int 5)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x32  c.sub a5,a5,a4  (creg 7 = a5, creg 6 = a4) *)
Lemma uddc_8f99 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8f99 : mword 16)) s
  = Some (C_SUB (Cregidx (mword_of_int 7), Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.


(* 0x3c  c.mv a1,a4 *)
Lemma uddc_85ba s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85ba : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x42  c.j -0x1c  (offset/2 = -14; 11-bit residue 2034) *)
(* [cdec_b7d5] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all five are uvmdealloc's own.           *)
(* ===================================================================== *)

(* 0x0c  bgeu a2,a1,+0x1a  -- the [newsz >= oldsz] early-out *)
Lemma uddb_00b67d63 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b67d63 : mword 32)) s
  = Some (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BGEU), s).
Proof. decode_bridge_ms. Qed.


(* 0x22  bltu a4,a5,+0x10  -- PGROUNDUP(newsz) < PGROUNDUP(oldsz) *)
Lemma uddb_00f76863 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00f76863 : mword 32)) s
  = Some (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU), s).
Proof. decode_bridge_ms. Qed.

(* 0x38  sext.w a2,a5  = ADDIW a2,a5,0 *)
Lemma uddb_0007861b s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0007861b : mword 32)) s
  = Some (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12)), s).
Proof. decode_bridge_ms. Qed.

(* 0x3e  jal ra,uvmunmap  (0x800012c6 -> 0x800011fe is -200) *)
Lemma uddb_f39ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf39ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096952 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmdeallocInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.


  (* --- prologue: 32-byte frame saving ra/s0/s1 ------------------------ *)

  Lemma udi_00 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma udi_02 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma udi_04 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma udi_06 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma udi_08 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* --- s1 := oldsz, then the [newsz >= oldsz] early-out --------------- *)

  Lemma udi_0a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x0a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x0a)%Z (mword_of_int 0x84ae : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x0a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 9), ADD)) cdec_84ae exec_execute_C_MV. Qed.

  Lemma udi_0c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x0c) : mword 64) false (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BGEU)).
  Proof. mk_base (KernelSyms.uvmdealloc + 0x0c)%Z (mword_of_int 0x00b67d63 : mword 32)
    (mword_of_int (KernelSyms.uvmdealloc + 0x0c) : mword 64) (BTYPE (mword_of_int 26 : mword 13, Regidx (mword_of_int 11), Regidx (mword_of_int 12), BGEU)) uddb_00b67d63. Qed.

  (* --- the two PGROUNDUPs and the [something to unmap] test ----------- *)

  Lemma udi_10 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x10)%Z (mword_of_int 0x84b2 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 12), zreg, Regidx (mword_of_int 9), ADD)) cdec_84b2 exec_execute_C_MV. Qed.

  Lemma udi_12 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x12) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x12)%Z (mword_of_int 0x6785 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x12) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 15), LUI)) cdec_6785 exec_execute_C_LUI. Qed.

  Lemma udi_14 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x14) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x14)%Z (mword_of_int 0x17fd : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x14) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADDI)) cdec_17fd exec_execute_C_ADDI. Qed.

  Lemma udi_16 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x16) : mword 64) false (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)).
  Proof. mk_base (KernelSyms.uvmdealloc + 0x16)%Z (mword_of_int 0x00f60733 : mword 32)
    (mword_of_int (KernelSyms.uvmdealloc + 0x16) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 12), Regidx (mword_of_int 14), ADD)) bdec_00f60733. Qed.

  Lemma udi_1a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x1a) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 13), LUI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x1a)%Z (mword_of_int 0x76fd : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x1a) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 63 : mword 6), Regidx (mword_of_int 13), LUI)) uddc_76fd exec_execute_C_LUI. Qed.

  Lemma udi_1c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x1c) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 6)), AND)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x1c)%Z (mword_of_int 0x8f75 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x1c) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 6)), AND)) cdec_8f75 exec_execute_C_AND. Qed.

  Lemma udi_1e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x1e) : mword 64) true (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x1e)%Z (mword_of_int 0x97ae : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x1e) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 15), Regidx (mword_of_int 15), ADD)) uddc_97ae exec_execute_C_ADD. Qed.

  Lemma udi_20 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x20) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), AND)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x20)%Z (mword_of_int 0x8ff5 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x20) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 5)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), AND)) uddc_8ff5 exec_execute_C_AND. Qed.

  Lemma udi_22 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x22) : mword 64) false (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)).
  Proof. mk_base (KernelSyms.uvmdealloc + 0x22)%Z (mword_of_int 0x00f76863 : mword 32)
    (mword_of_int (KernelSyms.uvmdealloc + 0x22) : mword 64) (BTYPE (mword_of_int 16 : mword 13, Regidx (mword_of_int 15), Regidx (mword_of_int 14), BLTU)) uddb_00f76863. Qed.

  (* --- the epilogue, joined by the early-out, the unmap arm and 0x22 -- *)

  Lemma udi_26 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x26) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x26)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x26) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma udi_28 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x28) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x28)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x28) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma udi_2a : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x2a)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma udi_2c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x2c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x2c)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x2c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma udi_2e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x2e) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x2e)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x2e) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma udi_30 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x30) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x30)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x30) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* --- the unmap arm: npages, do_free = 1, uvmunmap() ----------------- *)

  Lemma udi_32 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x32) : mword 64) true (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SUB)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x32)%Z (mword_of_int 0x8f99 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x32) : mword 64) (RTYPE (creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SUB)) uddc_8f99 exec_execute_C_SUB. Qed.

  Lemma udi_34 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x34) : mword 64) true (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x34)%Z (mword_of_int 0x83b1 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x34) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83b1 exec_execute_C_SRLI. Qed.

  Lemma udi_36 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x36) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x36)%Z (mword_of_int 0x4685 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x36) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4685 exec_execute_C_LI. Qed.

  Lemma udi_38 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x38) : mword 64) false (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12))).
  Proof. mk_base (KernelSyms.uvmdealloc + 0x38)%Z (mword_of_int 0x0007861b : mword 32)
    (mword_of_int (KernelSyms.uvmdealloc + 0x38) : mword 64) (ADDIW (mword_of_int 0 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 12))) uddb_0007861b. Qed.

  Lemma udi_3c : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x3c) : mword 64) true (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x3c)%Z (mword_of_int 0x85ba : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x3c) : mword 64) (RTYPE (Regidx (mword_of_int 14), zreg, Regidx (mword_of_int 11), ADD)) uddc_85ba exec_execute_C_MV. Qed.

  Lemma udi_3e : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64) false (JAL (mword_of_int 2096952 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.uvmdealloc + 0x3e)%Z (mword_of_int 0xf39ff0ef : mword 32)
    (mword_of_int (KernelSyms.uvmdealloc + 0x3e) : mword 64) (JAL (mword_of_int 2096952 : mword 21, Regidx (mword_of_int 1))) uddb_f39ff0ef. Qed.

  Lemma udi_42 : kernel_text -∗ instr (mword_of_int (KernelSyms.uvmdealloc + 0x42) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.uvmdealloc + 0x42)%Z (mword_of_int 0xb7d5 : mword 16)
    (mword_of_int (KernelSyms.uvmdealloc + 0x42) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2034 : mword 11) ('b"0")), zreg)) cdec_b7d5 exec_execute_C_J. Qed.

End UvmdeallocInstrs.

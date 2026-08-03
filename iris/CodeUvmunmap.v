(* CodeUvmunmap.v -- the instruction-DECODE layer for xv6's uvmunmap().

     uvmunmap @ 0x800011fe .. 0x80001287   (offsets 0x00 .. 0x88, 56 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([uui_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the thirteen 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>]; uvmunmap's own words are local, named [uudc_<word>]
   (compressed) / [uudb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/vm.c's
   uvmunmap(pagetable_t, uint64 va, uint64 npages, int do_free)):

     0x00 7139       c.addi16sp sp,-64      # 64-byte frame (8 slots)
     0x02 fc06       c.sdsp ra,56(sp)
     0x04 f822       c.sdsp s0,48(sp)
     0x06 0080       c.addi4spn s0,sp,64
     0x08 03459793   slli  a5,a1,0x34       # va << 52: the alignment test
     0x0c e38d       c.bnez a5,+0x22        # -> 0x2e  (panic arm; dead)
     0x0e f04a       c.sdsp s2,32(sp)
     0x10 ec4e       c.sdsp s3,24(sp)
     0x12 e852       c.sdsp s4,16(sp)
     0x14 e456       c.sdsp s5,8(sp)
     0x16 e05a       c.sdsp s6,0(sp)
     0x18 8a2a       c.mv   s4,a0           # s4 := pagetable
     0x1a 892e       c.mv   s2,a1           # s2 := a  (the cursor va)
     0x1c 8ab6       c.mv   s5,a3           # s5 := do_free
     0x1e 0632       c.slli a2,a2,0xc       # npages << 12
     0x20 00b609b3   add   s3,a2,a1         # s3 := va + npages*PGSIZE
     0x24 6b05       c.lui  s6,0x1          # s6 := 4096
     0x26 0535f963   bgeu  a1,s3,+0x52      # -> 0x78, npages == 0
     0x2a f426       c.sdsp s1,40(sp)       # s1 saved only if the loop runs
     0x2c a015       c.j    +0x24           # -> 0x50 (loop head)
     0x2e f426       c.sdsp s1,40(sp)       # --- the panic arm (0x2e..0x45)
     0x30 f04a       c.sdsp s2,32(sp)
     0x32 ec4e       c.sdsp s3,24(sp)
     0x34 e852       c.sdsp s4,16(sp)
     0x36 e456       c.sdsp s5,8(sp)
     0x38 e05a       c.sdsp s6,0(sp)
     0x3a 00006517   auipc a0,0x6
     0x3e ee850513   addi  a0,a0,-280       # the panic message
     0x42 de6ff0ef   jal   ra,panic         # 0x80000826
     0x46 0004b023   sd    zero,0(s1)       # *pte = 0  <- loop tail joins here
     0x4a 995a       c.add  s2,s2,s6        # a += PGSIZE
     0x4c 03397563   bgeu  s2,s3,+0x2a      # -> 0x76, loop exit
     0x50 4601       c.li   a2,0            # --- loop head: walk(pt, a, 0)
     0x52 85ca       c.mv   a1,s2
     0x54 8552       c.mv   a0,s4
     0x56 d09ff0ef   jal   ra,walk          # 0x80000f5c
     0x5a 84aa       c.mv   s1,a0           # s1 := pte
     0x5c d57d       c.beqz a0,-0x12        # -> 0x4a, no leaf page: continue
     0x5e 611c       c.ld   a5,0(a0)        # a5 := *pte
     0x60 0017f713   andi  a4,a5,1          # PTE_V
     0x64 d37d       c.beqz a4,-0x1a        # -> 0x4a, not mapped: continue
     0x66 fe0a80e3   beqz  s5,-0x20         # -> 0x46, do_free == 0
     0x6a 83a9       c.srli a5,a5,0xa       # --- PTE2PA
     0x6c 00c79513   slli  a0,a5,0xc
     0x70 fd8ff0ef   jal   ra,kfree         # 0x80000a46
     0x74 bfc9       c.j    -0x2e           # -> 0x46
     0x76 74a2       c.ldsp s1,40(sp)       # --- epilogue
     0x78 7902       c.ldsp s2,32(sp)
     0x7a 69e2       c.ldsp s3,24(sp)
     0x7c 6a42       c.ldsp s4,16(sp)
     0x7e 6aa2       c.ldsp s5,8(sp)
     0x80 6b02       c.ldsp s6,0(sp)
     0x82 70e2       c.ldsp ra,56(sp)
     0x84 7442       c.ldsp s0,48(sp)
     0x86 6121       c.addi16sp sp,64
     0x88 8082       c.ret

   Note the shrink-wrapped prologue: ra/s0 are pushed unconditionally, but
   s2..s6 are pushed TWICE in the text -- once on the fall-through at
   0x0e..0x16 and once on the [va & 0xfff != 0] panic arm at 0x30..0x38 --
   and s1 is pushed at 0x2a (loop runs) or 0x2e (panic).  The panic arm
   0x2e..0x45 is dead for a page-aligned [va] but still has to decode.  The
   epilogue at 0x76..0x88 is fed by two arms: the npages == 0 branch at 0x26
   enters at 0x78 (s1 was never saved) and the loop exit at 0x4c enters at
   0x76 (restoring s1 first).

   All branch/jump immediates below are the DECODER's positive residues: the
   AST arg for BTYPE/JAL is the BYTE offset residue, while for
   C_J/C_BEQZ/C_BNEZ it is the offset/2 residue.  So the backward [c.beqz]s
   are 247 / 243 (2^8 complements of -9 / -13 half-words), the backward
   [c.j] is 2025 (2^11 complement of -23 half-words), the backward [beq] is
   8160 (2^13 complement of -32 bytes) and the three backward [jal]s are
   2094566 / 2096392 / 2095064 (2^21 complements of -2586 / -760 / -2088). *)
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
(* Compressed decode facts for uvmunmap's own words.                      *)
(* ===================================================================== *)

(* 0x00  c.addi16sp sp,-64  -- [cdec_7139] (KernelRvcDecode.v) *)
(* 0x02  c.sdsp ra,56(sp)   -- [cdec_fc06] (KernelRvcDecode.v) *)
(* 0x04  c.sdsp s0,48(sp)   -- [cdec_f822] (KernelRvcDecode.v) *)
(* 0x06  c.addi4spn s0,sp,64 -- [cdec_0080] (KernelRvcDecode.v) *)
(* 0x0e / 0x30  c.sdsp s2,32(sp) -- [cdec_f04a] (KernelRvcDecode.v) *)
(* 0x10 / 0x32  c.sdsp s3,24(sp) -- [cdec_ec4e] (KernelRvcDecode.v) *)
(* 0x12 / 0x34  c.sdsp s4,16(sp) -- [cdec_e852] (KernelRvcDecode.v) *)
(* 0x14 / 0x36  c.sdsp s5,8(sp)  -- [cdec_e456] (KernelRvcDecode.v) *)
(* 0x16 / 0x38  c.sdsp s6,0(sp)  -- [cdec_e05a] (KernelRvcDecode.v) *)
(* 0x18  c.mv s4,a0        -- [cdec_8a2a] (KernelRvcDecode.v) *)
(* 0x1a  c.mv s2,a1        -- [cdec_892e] (KernelRvcDecode.v) *)
(* 0x24  c.lui s6,0x1      -- [cdec_6b05] (KernelRvcDecode.v) *)
(* 0x2a / 0x2e  c.sdsp s1,40(sp) -- [cdec_f426] (KernelRvcDecode.v) *)
(* 0x50  c.li a2,0         -- [cdec_4601] (KernelRvcDecode.v) *)
(* 0x52  c.mv a1,s2        -- [cdec_85ca] (KernelRvcDecode.v) *)
(* 0x54  c.mv a0,s4        -- [cdec_8552] (KernelRvcDecode.v) *)
(* 0x5a  c.mv s1,a0        -- [cdec_84aa] (KernelRvcDecode.v) *)
(* 0x5e  c.ld a5,0(a0)     -- [cdec_611c] (KernelRvcDecode.v) *)
(* 0x76  c.ldsp s1,40(sp)  -- [cdec_74a2] (KernelRvcDecode.v) *)
(* 0x78  c.ldsp s2,32(sp)  -- [cdec_7902] (KernelRvcDecode.v) *)
(* 0x7a  c.ldsp s3,24(sp)  -- [cdec_69e2] (KernelRvcDecode.v) *)
(* 0x7c  c.ldsp s4,16(sp)  -- [cdec_6a42] (KernelRvcDecode.v) *)
(* 0x7e  c.ldsp s5,8(sp)   -- [cdec_6aa2] (KernelRvcDecode.v) *)
(* 0x80  c.ldsp s6,0(sp)   -- [cdec_6b02] (KernelRvcDecode.v) *)
(* 0x82  c.ldsp ra,56(sp)  -- [cdec_70e2] (KernelRvcDecode.v) *)
(* 0x84  c.ldsp s0,48(sp)  -- [cdec_7442] (KernelRvcDecode.v) *)
(* 0x86  c.addi16sp sp,64  -- [cdec_6121] (KernelRvcDecode.v) *)
(* 0x88  c.ret             -- [cdec_8082] (KernelRvcDecode.v) *)

(* 0x0c  c.bnez a5,+0x22  (offset/2 = 17) *)
Lemma uudc_e38d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe38d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 17, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x1c  c.mv s5,a3 *)
(* [cdec_8ab6] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1e  c.slli a2,a2,0xc *)
Lemma uudc_0632 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0632 : mword 16)) s
  = Some (C_SLLI (mword_of_int 12, Regidx (mword_of_int 12)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2c  c.j +0x24  (offset/2 = 18) *)
(* [cdec_a015] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x4a  c.add s2,s2,s6 *)
Lemma uudc_995a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x995a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x5c  c.beqz a0,-0x12  (offset/2 = -9; 8-bit residue 247) *)
Lemma uudc_d57d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd57d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 247, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x64  c.beqz a4,-0x1a  (offset/2 = -13; 8-bit residue 243) *)
Lemma uudc_d37d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xd37d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 243, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x6a  c.srli a5,a5,0xa  -- the first half of PTE2PA *)
(* [cdec_83a9] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x74  c.j -0x2e  (offset/2 = -23; 11-bit residue 2025) *)
(* [cdec_bfc9] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* ===================================================================== *)
(* Base (4-byte) decode facts -- all thirteen are uvmunmap's own.         *)
(* ===================================================================== *)

(* 0x08  slli a5,a1,0x34  -- (va << 52) != 0 is the "not page aligned" test *)
(* [bdec_03459793] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x20  add s3,a2,a1  -- the loop bound va + npages*PGSIZE *)
Lemma uudb_00b609b3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00b609b3 : mword 32)) s
  = Some (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 19), ADD), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  bgeu a1,s3,+0x52  -- npages == 0 (rs1 = a1, rs2 = s3) *)
Lemma uudb_0535f963 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0535f963 : mword 32)) s
  = Some (BTYPE (mword_of_int 82 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 11), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x3a  auipc a0,0x6  -- first half of the panic-message address *)
(* [bdec_00006517] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x3e  addi a0,a0,-280  (12-bit residue 3816) *)
Lemma uudb_ee850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xee850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3816 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x42  jal ra,panic  (0x80001240 -> 0x80000826 is -2586) *)
Lemma uudb_de6ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xde6ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094566 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


(* 0x4c  bgeu s2,s3,+0x2a  -- the loop-exit test (rs1 = s2, rs2 = s3) *)
Lemma uudb_03397563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03397563 : mword 32)) s
  = Some (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 18), BGEU), s).
Proof. decode_bridge_ms. Qed.

(* 0x56  jal ra,walk  (0x80001254 -> 0x80000f5c is -760) *)
Lemma uudb_d09ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd09ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096392 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.


(* 0x66  beq s5,zero,-0x20  -- do_free == 0 (13-bit residue 8160) *)
Lemma uudb_fe0a80e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe0a80e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8160 : mword 13, zreg, Regidx (mword_of_int 21), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x6c  slli a0,a5,0xc  -- the second half of PTE2PA *)
(* [bdec_00c79513] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x70  jal ra,kfree  (0x8000126e -> 0x80000a46 is -2088) *)
Lemma uudb_fd8ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd8ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095064 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section UvmunmapInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation UU := KernelSyms.uvmunmap.

  (* --- prologue: ra/s0 always, then the alignment test ---------------- *)

  Lemma uui_00 : kernel_text -∗ instr (mword_of_int (UU + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UU + 0x00)%Z (mword_of_int 0x7139 : mword 16)
    (mword_of_int (UU + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.

  Lemma uui_02 : kernel_text -∗ instr (mword_of_int (UU + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (UU + 0x02)%Z (mword_of_int 0xfc06 : mword 16)
    (mword_of_int (UU + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.

  Lemma uui_04 : kernel_text -∗ instr (mword_of_int (UU + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (UU + 0x04)%Z (mword_of_int 0xf822 : mword 16)
    (mword_of_int (UU + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.

  Lemma uui_06 : kernel_text -∗ instr (mword_of_int (UU + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (UU + 0x06)%Z (mword_of_int 0x0080 : mword 16)
    (mword_of_int (UU + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.

  Lemma uui_08 : kernel_text -∗ instr (mword_of_int (UU + 0x08) : mword 64) false (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_base (UU + 0x08)%Z (mword_of_int 0x03459793 : mword 32)
    (mword_of_int (UU + 0x08) : mword 64) (SHIFTIOP (mword_of_int 52 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 15), SLLI)) bdec_03459793. Qed.

  Lemma uui_0c : kernel_text -∗ instr (mword_of_int (UU + 0x0c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)).
  Proof. mk_rvc (UU + 0x0c)%Z (mword_of_int 0xe38d : mword 16)
    (mword_of_int (UU + 0x0c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 17 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BNE)) uudc_e38d exec_execute_C_BNEZ. Qed.

  (* --- the aligned fall-through: save s2..s6 and set up the loop ------ *)

  Lemma uui_0e : kernel_text -∗ instr (mword_of_int (UU + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (UU + 0x0e)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (UU + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  Lemma uui_10 : kernel_text -∗ instr (mword_of_int (UU + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (UU + 0x10)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (UU + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  Lemma uui_12 : kernel_text -∗ instr (mword_of_int (UU + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (UU + 0x12)%Z (mword_of_int 0xe852 : mword 16)
    (mword_of_int (UU + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.

  Lemma uui_14 : kernel_text -∗ instr (mword_of_int (UU + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (UU + 0x14)%Z (mword_of_int 0xe456 : mword 16)
    (mword_of_int (UU + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.

  Lemma uui_16 : kernel_text -∗ instr (mword_of_int (UU + 0x16) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (UU + 0x16)%Z (mword_of_int 0xe05a : mword 16)
    (mword_of_int (UU + 0x16) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e05a exec_execute_C_SDSP. Qed.

  Lemma uui_18 : kernel_text -∗ instr (mword_of_int (UU + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (UU + 0x18)%Z (mword_of_int 0x8a2a : mword 16)
    (mword_of_int (UU + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.

  Lemma uui_1a : kernel_text -∗ instr (mword_of_int (UU + 0x1a) : mword 64) true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (UU + 0x1a)%Z (mword_of_int 0x892e : mword 16)
    (mword_of_int (UU + 0x1a) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma uui_1c : kernel_text -∗ instr (mword_of_int (UU + 0x1c) : mword 64) true (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (UU + 0x1c)%Z (mword_of_int 0x8ab6 : mword 16)
    (mword_of_int (UU + 0x1c) : mword 64) (RTYPE (Regidx (mword_of_int 13), zreg, Regidx (mword_of_int 21), ADD)) cdec_8ab6 exec_execute_C_MV. Qed.

  Lemma uui_1e : kernel_text -∗ instr (mword_of_int (UU + 0x1e) : mword 64) true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)).
  Proof. mk_rvc (UU + 0x1e)%Z (mword_of_int 0x0632 : mword 16)
    (mword_of_int (UU + 0x1e) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 12), Regidx (mword_of_int 12), SLLI)) uudc_0632 exec_execute_C_SLLI. Qed.

  Lemma uui_20 : kernel_text -∗ instr (mword_of_int (UU + 0x20) : mword 64) false (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 19), ADD)).
  Proof. mk_base (UU + 0x20)%Z (mword_of_int 0x00b609b3 : mword 32)
    (mword_of_int (UU + 0x20) : mword 64) (RTYPE (Regidx (mword_of_int 11), Regidx (mword_of_int 12), Regidx (mword_of_int 19), ADD)) uudb_00b609b3. Qed.

  Lemma uui_24 : kernel_text -∗ instr (mword_of_int (UU + 0x24) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)).
  Proof. mk_rvc (UU + 0x24)%Z (mword_of_int 0x6b05 : mword 16)
    (mword_of_int (UU + 0x24) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 22), LUI)) cdec_6b05 exec_execute_C_LUI. Qed.

  Lemma uui_26 : kernel_text -∗ instr (mword_of_int (UU + 0x26) : mword 64) false (BTYPE (mword_of_int 82 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 11), BGEU)).
  Proof. mk_base (UU + 0x26)%Z (mword_of_int 0x0535f963 : mword 32)
    (mword_of_int (UU + 0x26) : mword 64) (BTYPE (mword_of_int 82 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 11), BGEU)) uudb_0535f963. Qed.

  Lemma uui_2a : kernel_text -∗ instr (mword_of_int (UU + 0x2a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UU + 0x2a)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (UU + 0x2a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  Lemma uui_2c : kernel_text -∗ instr (mword_of_int (UU + 0x2c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UU + 0x2c)%Z (mword_of_int 0xa015 : mword 16)
    (mword_of_int (UU + 0x2c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 18 : mword 11) ('b"0")), zreg)) cdec_a015 exec_execute_C_J. Qed.

  (* --- the panic arm, 0x2e..0x45 (dead for a page-aligned va) --------- *)

  Lemma uui_2e : kernel_text -∗ instr (mword_of_int (UU + 0x2e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (UU + 0x2e)%Z (mword_of_int 0xf426 : mword 16)
    (mword_of_int (UU + 0x2e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.

  Lemma uui_30 : kernel_text -∗ instr (mword_of_int (UU + 0x30) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (UU + 0x30)%Z (mword_of_int 0xf04a : mword 16)
    (mword_of_int (UU + 0x30) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.

  Lemma uui_32 : kernel_text -∗ instr (mword_of_int (UU + 0x32) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (UU + 0x32)%Z (mword_of_int 0xec4e : mword 16)
    (mword_of_int (UU + 0x32) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.

  Lemma uui_34 : kernel_text -∗ instr (mword_of_int (UU + 0x34) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (UU + 0x34)%Z (mword_of_int 0xe852 : mword 16)
    (mword_of_int (UU + 0x34) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.

  Lemma uui_36 : kernel_text -∗ instr (mword_of_int (UU + 0x36) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (UU + 0x36)%Z (mword_of_int 0xe456 : mword 16)
    (mword_of_int (UU + 0x36) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.

  Lemma uui_38 : kernel_text -∗ instr (mword_of_int (UU + 0x38) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (UU + 0x38)%Z (mword_of_int 0xe05a : mword 16)
    (mword_of_int (UU + 0x38) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e05a exec_execute_C_SDSP. Qed.

  Lemma uui_3a : kernel_text -∗ instr (mword_of_int (UU + 0x3a) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (UU + 0x3a)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (UU + 0x3a) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma uui_3e : kernel_text -∗ instr (mword_of_int (UU + 0x3e) : mword 64) false (ITYPE (mword_of_int 3816 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (UU + 0x3e)%Z (mword_of_int 0xee850513 : mword 32)
    (mword_of_int (UU + 0x3e) : mword 64) (ITYPE (mword_of_int 3816 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) uudb_ee850513. Qed.

  Lemma uui_42 : kernel_text -∗ instr (mword_of_int (UU + 0x42) : mword 64) false (JAL (mword_of_int 2094566 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UU + 0x42)%Z (mword_of_int 0xde6ff0ef : mword 32)
    (mword_of_int (UU + 0x42) : mword 64) (JAL (mword_of_int 2094566 : mword 21, Regidx (mword_of_int 1))) uudb_de6ff0ef. Qed.

  (* --- the loop tail: *pte = 0, a += PGSIZE, re-test ------------------ *)

  Lemma uui_46 : kernel_text -∗ instr (mword_of_int (UU + 0x46) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (UU + 0x46)%Z (mword_of_int 0x0004b023 : mword 32)
    (mword_of_int (UU + 0x46) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)) bdec_0004b023. Qed.

  Lemma uui_4a : kernel_text -∗ instr (mword_of_int (UU + 0x4a) : mword 64) true (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (UU + 0x4a)%Z (mword_of_int 0x995a : mword 16)
    (mword_of_int (UU + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) uudc_995a exec_execute_C_ADD. Qed.

  Lemma uui_4c : kernel_text -∗ instr (mword_of_int (UU + 0x4c) : mword 64) false (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 18), BGEU)).
  Proof. mk_base (UU + 0x4c)%Z (mword_of_int 0x03397563 : mword 32)
    (mword_of_int (UU + 0x4c) : mword 64) (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 18), BGEU)) uudb_03397563. Qed.

  (* --- the loop head: walk(pagetable, a, 0) --------------------------- *)

  Lemma uui_50 : kernel_text -∗ instr (mword_of_int (UU + 0x50) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (UU + 0x50)%Z (mword_of_int 0x4601 : mword 16)
    (mword_of_int (UU + 0x50) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  Lemma uui_52 : kernel_text -∗ instr (mword_of_int (UU + 0x52) : mword 64) true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (UU + 0x52)%Z (mword_of_int 0x85ca : mword 16)
    (mword_of_int (UU + 0x52) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma uui_54 : kernel_text -∗ instr (mword_of_int (UU + 0x54) : mword 64) true (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (UU + 0x54)%Z (mword_of_int 0x8552 : mword 16)
    (mword_of_int (UU + 0x54) : mword 64) (RTYPE (Regidx (mword_of_int 20), zreg, Regidx (mword_of_int 10), ADD)) cdec_8552 exec_execute_C_MV. Qed.

  Lemma uui_56 : kernel_text -∗ instr (mword_of_int (UU + 0x56) : mword 64) false (JAL (mword_of_int 2096392 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UU + 0x56)%Z (mword_of_int 0xd09ff0ef : mword 32)
    (mword_of_int (UU + 0x56) : mword 64) (JAL (mword_of_int 2096392 : mword 21, Regidx (mword_of_int 1))) uudb_d09ff0ef. Qed.

  Lemma uui_5a : kernel_text -∗ instr (mword_of_int (UU + 0x5a) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (UU + 0x5a)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (UU + 0x5a) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma uui_5c : kernel_text -∗ instr (mword_of_int (UU + 0x5c) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 247 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (UU + 0x5c)%Z (mword_of_int 0xd57d : mword 16)
    (mword_of_int (UU + 0x5c) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 247 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) uudc_d57d exec_execute_C_BEQZ. Qed.

  (* --- the PTE_V test and the do_free test --------------------------- *)

  Lemma uui_5e : kernel_text -∗ instr (mword_of_int (UU + 0x5e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (UU + 0x5e)%Z (mword_of_int 0x611c : mword 16)
    (mword_of_int (UU + 0x5e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 2)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) cdec_611c exec_execute_C_LD. Qed.

  Lemma uui_60 : kernel_text -∗ instr (mword_of_int (UU + 0x60) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_base (UU + 0x60)%Z (mword_of_int 0x0017f713 : mword 32)
    (mword_of_int (UU + 0x60) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)) bdec_0017f713. Qed.

  Lemma uui_64 : kernel_text -∗ instr (mword_of_int (UU + 0x64) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).
  Proof. mk_rvc (UU + 0x64)%Z (mword_of_int 0xd37d : mword 16)
    (mword_of_int (UU + 0x64) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 243 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) uudc_d37d exec_execute_C_BEQZ. Qed.

  Lemma uui_66 : kernel_text -∗ instr (mword_of_int (UU + 0x66) : mword 64) false (BTYPE (mword_of_int 8160 : mword 13, zreg, Regidx (mword_of_int 21), BEQ)).
  Proof. mk_base (UU + 0x66)%Z (mword_of_int 0xfe0a80e3 : mword 32)
    (mword_of_int (UU + 0x66) : mword 64) (BTYPE (mword_of_int 8160 : mword 13, zreg, Regidx (mword_of_int 21), BEQ)) uudb_fe0a80e3. Qed.

  (* --- do_free: PTE2PA and kfree ------------------------------------- *)

  Lemma uui_6a : kernel_text -∗ instr (mword_of_int (UU + 0x6a) : mword 64) true (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (UU + 0x6a)%Z (mword_of_int 0x83a9 : mword 16)
    (mword_of_int (UU + 0x6a) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83a9 exec_execute_C_SRLI. Qed.

  Lemma uui_6c : kernel_text -∗ instr (mword_of_int (UU + 0x6c) : mword 64) false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)).
  Proof. mk_base (UU + 0x6c)%Z (mword_of_int 0x00c79513 : mword 32)
    (mword_of_int (UU + 0x6c) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)) bdec_00c79513. Qed.

  Lemma uui_70 : kernel_text -∗ instr (mword_of_int (UU + 0x70) : mword 64) false (JAL (mword_of_int 2095064 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (UU + 0x70)%Z (mword_of_int 0xfd8ff0ef : mword 32)
    (mword_of_int (UU + 0x70) : mword 64) (JAL (mword_of_int 2095064 : mword 21, Regidx (mword_of_int 1))) uudb_fd8ff0ef. Qed.

  Lemma uui_74 : kernel_text -∗ instr (mword_of_int (UU + 0x74) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (UU + 0x74)%Z (mword_of_int 0xbfc9 : mword 16)
    (mword_of_int (UU + 0x74) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2025 : mword 11) ('b"0")), zreg)) cdec_bfc9 exec_execute_C_J. Qed.

  (* --- the epilogue: 0x76 from the loop exit, 0x78 from npages == 0 --- *)

  Lemma uui_76 : kernel_text -∗ instr (mword_of_int (UU + 0x76) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (UU + 0x76)%Z (mword_of_int 0x74a2 : mword 16)
    (mword_of_int (UU + 0x76) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.

  Lemma uui_78 : kernel_text -∗ instr (mword_of_int (UU + 0x78) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (UU + 0x78)%Z (mword_of_int 0x7902 : mword 16)
    (mword_of_int (UU + 0x78) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.

  Lemma uui_7a : kernel_text -∗ instr (mword_of_int (UU + 0x7a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (UU + 0x7a)%Z (mword_of_int 0x69e2 : mword 16)
    (mword_of_int (UU + 0x7a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.

  Lemma uui_7c : kernel_text -∗ instr (mword_of_int (UU + 0x7c) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (UU + 0x7c)%Z (mword_of_int 0x6a42 : mword 16)
    (mword_of_int (UU + 0x7c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 20), false, 8)) cdec_6a42 exec_execute_C_LDSP. Qed.

  Lemma uui_7e : kernel_text -∗ instr (mword_of_int (UU + 0x7e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (UU + 0x7e)%Z (mword_of_int 0x6aa2 : mword 16)
    (mword_of_int (UU + 0x7e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 21), false, 8)) cdec_6aa2 exec_execute_C_LDSP. Qed.

  Lemma uui_80 : kernel_text -∗ instr (mword_of_int (UU + 0x80) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)).
  Proof. mk_rvc (UU + 0x80)%Z (mword_of_int 0x6b02 : mword 16)
    (mword_of_int (UU + 0x80) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 22), false, 8)) cdec_6b02 exec_execute_C_LDSP. Qed.

  Lemma uui_82 : kernel_text -∗ instr (mword_of_int (UU + 0x82) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (UU + 0x82)%Z (mword_of_int 0x70e2 : mword 16)
    (mword_of_int (UU + 0x82) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.

  Lemma uui_84 : kernel_text -∗ instr (mword_of_int (UU + 0x84) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (UU + 0x84)%Z (mword_of_int 0x7442 : mword 16)
    (mword_of_int (UU + 0x84) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.

  Lemma uui_86 : kernel_text -∗ instr (mword_of_int (UU + 0x86) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (UU + 0x86)%Z (mword_of_int 0x6121 : mword 16)
    (mword_of_int (UU + 0x86) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.

  Lemma uui_88 : kernel_text -∗ instr (mword_of_int (UU + 0x88) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (UU + 0x88)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (UU + 0x88) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End UvmunmapInstrs.

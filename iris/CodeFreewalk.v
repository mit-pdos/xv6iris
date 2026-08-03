(* CodeFreewalk.v -- the instruction-DECODE layer for xv6's freewalk().

     freewalk @ 0x80001376 .. 0x800013d1   (offsets 0x00 .. 0x5a, 36 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([fwi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the ten 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode as
   [cdec_<word>] / KernelBaseDecode as [bdec_<word>]; freewalk's own words are
   local, named [fwdc_<word>] (compressed) / [fwdb_<word>] (base).

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm -- which has drifted by 0xe bytes; the C is kernel/vm.c's
   [void freewalk(pagetable_t pagetable)], a0 = pagetable):

     0x00 7179       c.addi16sp sp,-48      # 48-byte frame (6 slots)
     0x02 f406       c.sdsp ra,40(sp)
     0x04 f022       c.sdsp s0,32(sp)
     0x06 ec26       c.sdsp s1,24(sp)
     0x08 e84a       c.sdsp s2,16(sp)
     0x0a e44e       c.sdsp s3,8(sp)
     0x0c 1800       c.addi4spn s0,sp,48
     0x0e 89aa       c.mv   s3,a0           # s3 := pagetable (kfree's arg)
     0x10 84aa       c.mv   s1,a0           # s1 := &pagetable[0], the cursor
     0x12 6905       c.lui  s2,0x1          # s2 := 4096
     0x14 992a       c.add  s2,s2,a0        # s2 := &pagetable[512], the limit
     0x16 a811       c.j    +0x14           # -> 0x2a, into the loop body
     0x18 00006517   auipc a0,0x6           # --- the panic arm (leaf pte)
     0x1c daa50513   addi  a0,a0,-598       # the "freewalk: leaf" message
     0x20 c90ff0ef   jal   ra,panic         # 0x80000826
     0x24 04a1       c.addi s1,s1,8         # --- loop tail: ++pte
     0x26 03248163   beq   s1,s2,+0x22      # -> 0x48, all 512 entries done
     0x2a 609c       c.ld   a5,0(s1)        # --- loop head: a5 := *pte
     0x2c 0017f713   andi  a4,a5,1          # PTE_V
     0x30 db75       c.beqz a4,-0x0c        # -> 0x24, not valid: next entry
     0x32 00e7f713   andi  a4,a5,14         # PTE_R|PTE_W|PTE_X
     0x36 f36d       c.bnez a4,-0x1e        # -> 0x18, a leaf: panic
     0x38 83a9       c.srli a5,a5,0xa       # --- PTE2PA: the child table
     0x3a 00c79513   slli  a0,a5,0xc
     0x3e fc3ff0ef   jal   ra,freewalk      # 0x80001376 -- the self-recursion
     0x42 0004b023   sd    zero,0(s1)       # *pte = 0
     0x46 bff9       c.j    -0x22           # -> 0x24, next entry
     0x48 854e       c.mv   a0,s3           # --- the exit: kfree(pagetable)
     0x4a e86ff0ef   jal   ra,kfree         # 0x80000a46
     0x4e 70a2       c.ldsp ra,40(sp)
     0x50 7402       c.ldsp s0,32(sp)
     0x52 64e2       c.ldsp s1,24(sp)
     0x54 6942       c.ldsp s2,16(sp)
     0x56 69a2       c.ldsp s3,8(sp)
     0x58 6145       c.addi16sp sp,48
     0x5a 8082       c.ret

   Note that the SAME 48-byte frame is traded in and back out by two
   [c.addi16sp]s (0x7179 / 0x6145), whose AST immediate is the displacement
   DIVIDED BY 16 as a 6-bit residue: -48/16 = -3 -> 61, +48/16 = 3.

   The branch/jump immediates below are the DECODER's positive residues, and
   the AST argument is the BYTE offset for BTYPE/JAL but the offset/2 residue
   for C_J / C_BEQZ / C_BNEZ:

     0x16 a811      C_J    arg(mword 11) = 10        (+0x14)      -> 0x2a
     0x20 c90ff0ef  JAL    arg(mword 21) = 2094224   (2^21 - 2928, panic)
     0x26 03248163  BTYPE  arg(mword 13) = 34        (+0x22)      -> 0x48
     0x30 db75      C_BEQZ arg(mword 8)  = 250       (2^8 - 6, -0x0c)  -> 0x24
     0x36 f36d      C_BNEZ arg(mword 8)  = 241       (2^8 - 15, -0x1e) -> 0x18
     0x3e fc3ff0ef  JAL    arg(mword 21) = 2097090   (2^21 - 62, freewalk)
     0x46 bff9      C_J    arg(mword 11) = 2031      (2^11 - 17, -0x22) -> 0x24
     0x4a e86ff0ef  JAL    arg(mword 21) = 2094726   (2^21 - 2426, kfree)  *)
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
(* Compressed decode facts for freewalk's own words.                      *)
(* ===================================================================== *)

(* 0x00  c.addi16sp sp,-48   -- [cdec_7179] (KernelRvcDecode.v) *)
(* 0x02  c.sdsp ra,40(sp)    -- [cdec_f406] (KernelRvcDecode.v) *)
(* 0x04  c.sdsp s0,32(sp)    -- [cdec_f022] (KernelRvcDecode.v) *)
(* 0x06  c.sdsp s1,24(sp)    -- [cdec_ec26] (KernelRvcDecode.v) *)
(* 0x08  c.sdsp s2,16(sp)    -- [cdec_e84a] (KernelRvcDecode.v) *)
(* 0x0a  c.sdsp s3,8(sp)     -- [cdec_e44e] (KernelRvcDecode.v) *)
(* 0x0c  c.addi4spn s0,sp,48 -- [cdec_1800] (KernelRvcDecode.v) *)
(* 0x0e  c.mv s3,a0          -- [cdec_89aa] (KernelRvcDecode.v) *)
(* 0x10  c.mv s1,a0          -- [cdec_84aa] (KernelRvcDecode.v) *)
(* 0x38  c.srli a5,a5,0xa    -- [cdec_83a9] (KernelRvcDecode.v) *)
(* 0x46  c.j -0x22           -- [cdec_bff9] (KernelRvcDecode.v) *)
(* 0x4e  c.ldsp ra,40(sp)    -- [cdec_70a2] (KernelRvcDecode.v) *)
(* 0x50  c.ldsp s0,32(sp)    -- [cdec_7402] (KernelRvcDecode.v) *)
(* 0x52  c.ldsp s1,24(sp)    -- [cdec_64e2] (KernelRvcDecode.v) *)
(* 0x54  c.ldsp s2,16(sp)    -- [cdec_6942] (KernelRvcDecode.v) *)
(* 0x56  c.ldsp s3,8(sp)     -- [cdec_69a2] (KernelRvcDecode.v) *)
(* 0x58  c.addi16sp sp,48    -- [cdec_6145] (KernelRvcDecode.v) *)
(* 0x5a  c.ret               -- [cdec_8082] (KernelRvcDecode.v) *)

(* 0x12  c.lui s2,0x1 *)
Lemma fwdc_6905 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6905 : mword 16)) s
  = Some (C_LUI (mword_of_int 1, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x14  c.add s2,s2,a0 *)
Lemma fwdc_992a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x992a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 18), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x16  c.j +0x14  (offset/2 = 10) *)
Lemma fwdc_a811 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa811 : mword 16)) s
  = Some (C_J (mword_of_int 10), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x24  c.addi s1,s1,8 *)
Lemma fwdc_04a1 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x04a1 : mword 16)) s
  = Some (C_ADDI (mword_of_int 8, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x2a  c.ld a5,0(s1)  (creg 1 = s1, creg 7 = a5) *)
Lemma fwdc_609c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x609c : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x30  c.beqz a4,-0x0c  (offset/2 = -6; 8-bit residue 250; creg 6 = a4) *)
Lemma fwdc_db75 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdb75 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 250, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x36  c.bnez a4,-0x1e  (offset/2 = -15; 8-bit residue 241; creg 6 = a4) *)
Lemma fwdc_f36d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf36d : mword 16)) s
  = Some (C_BNEZ (mword_of_int 241, Cregidx (mword_of_int 6)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x48  c.mv a0,s3 *)
Lemma fwdc_854e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x854e : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

(* 0x18  auipc a0,0x6 *)
(* [bdec_00006517] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x3a  slli a0,a5,0xc  (PTE2PA's << 12) *)
(* [bdec_00c79513] -- shared, see KernelRvcDecode.v / KernelBaseDecode.v *)

(* 0x1c  addi a0,a0,-598  -- the "freewalk: leaf" message (12-bit residue 3498) *)
Lemma fwdb_daa50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xdaa50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 3498 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x20  jal ra,panic  (0x80001396 -> 0x80000826 is -2928) *)
Lemma fwdb_c90ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc90ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094224 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x26  beq s1,s2,+0x22  -- the cursor reached &pagetable[512] *)
Lemma fwdb_03248163 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03248163 : mword 32)) s
  = Some (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ), s).
Proof. decode_bridge_ms. Qed.

(* 0x2c  andi a4,a5,1  -- PTE_V *)
Lemma fwdb_0017f713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0017f713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x32  andi a4,a5,14  -- PTE_R|PTE_W|PTE_X: a leaf? *)
Lemma fwdb_00e7f713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00e7f713 : mword 32)) s
  = Some (ITYPE (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI), s).
Proof. decode_bridge_ms. Qed.

(* 0x3e  jal ra,freewalk  -- the self-recursion (0x800013b4 -> 0x80001376, -62) *)
Lemma fwdb_fc3ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfc3ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2097090 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x42  sd zero,0(s1)  -- *pte = 0 *)
Lemma fwdb_0004b023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0004b023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8), s).
Proof. decode_bridge_ms. Qed.

(* 0x4a  jal ra,kfree  (0x800013c0 -> 0x80000a46 is -2426) *)
Lemma fwdb_e86ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe86ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094726 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FreewalkInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FW := KernelSyms.freewalk.

  (* --- prologue: 48-byte frame saving ra/s0/s1/s2/s3 ------------------ *)

  Lemma fwi_00 : kernel_text -∗ instr (mword_of_int (FW + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FW + 0x00)%Z (mword_of_int 0x7179 : mword 16)
    (mword_of_int (FW + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 61 : mword 6), sp, sp, ADDI)) cdec_7179 exec_execute_C_ADDI16SP. Qed.

  Lemma fwi_02 : kernel_text -∗ instr (mword_of_int (FW + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FW + 0x02)%Z (mword_of_int 0xf406 : mword 16)
    (mword_of_int (FW + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_f406 exec_execute_C_SDSP. Qed.

  Lemma fwi_04 : kernel_text -∗ instr (mword_of_int (FW + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FW + 0x04)%Z (mword_of_int 0xf022 : mword 16)
    (mword_of_int (FW + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_f022 exec_execute_C_SDSP. Qed.

  Lemma fwi_06 : kernel_text -∗ instr (mword_of_int (FW + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FW + 0x06)%Z (mword_of_int 0xec26 : mword 16)
    (mword_of_int (FW + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_ec26 exec_execute_C_SDSP. Qed.

  Lemma fwi_08 : kernel_text -∗ instr (mword_of_int (FW + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (FW + 0x08)%Z (mword_of_int 0xe84a : mword 16)
    (mword_of_int (FW + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e84a exec_execute_C_SDSP. Qed.

  Lemma fwi_0a : kernel_text -∗ instr (mword_of_int (FW + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (FW + 0x0a)%Z (mword_of_int 0xe44e : mword 16)
    (mword_of_int (FW + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_e44e exec_execute_C_SDSP. Qed.

  Lemma fwi_0c : kernel_text -∗ instr (mword_of_int (FW + 0x0c) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FW + 0x0c)%Z (mword_of_int 0x1800 : mword 16)
    (mword_of_int (FW + 0x0c) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 12 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1800 exec_execute_C_ADDI4SPN. Qed.

  (* --- s3 := pagetable, and the [s1, s2) cursor/limit pair ------------- *)

  Lemma fwi_0e : kernel_text -∗ instr (mword_of_int (FW + 0x0e) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)).
  Proof. mk_rvc (FW + 0x0e)%Z (mword_of_int 0x89aa : mword 16)
    (mword_of_int (FW + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 19), ADD)) cdec_89aa exec_execute_C_MV. Qed.

  Lemma fwi_10 : kernel_text -∗ instr (mword_of_int (FW + 0x10) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).
  Proof. mk_rvc (FW + 0x10)%Z (mword_of_int 0x84aa : mword 16)
    (mword_of_int (FW + 0x10) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma fwi_12 : kernel_text -∗ instr (mword_of_int (FW + 0x12) : mword 64) true (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), LUI)).
  Proof. mk_rvc (FW + 0x12)%Z (mword_of_int 0x6905 : mword 16)
    (mword_of_int (FW + 0x12) : mword 64) (UTYPE (sign_extend' 20 (mword_of_int 1 : mword 6), Regidx (mword_of_int 18), LUI)) fwdc_6905 exec_execute_C_LUI. Qed.

  Lemma fwi_14 : kernel_text -∗ instr (mword_of_int (FW + 0x14) : mword 64) true (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)).
  Proof. mk_rvc (FW + 0x14)%Z (mword_of_int 0x992a : mword 16)
    (mword_of_int (FW + 0x14) : mword 64) (RTYPE (Regidx (mword_of_int 10), Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADD)) fwdc_992a exec_execute_C_ADD. Qed.

  Lemma fwi_16 : kernel_text -∗ instr (mword_of_int (FW + 0x16) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FW + 0x16)%Z (mword_of_int 0xa811 : mword 16)
    (mword_of_int (FW + 0x16) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 10 : mword 11) ('b"0")), zreg)) fwdc_a811 exec_execute_C_J. Qed.

  (* --- the panic arm: a leaf PTE at a non-leaf level ------------------- *)

  Lemma fwi_18 : kernel_text -∗ instr (mword_of_int (FW + 0x18) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FW + 0x18)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (FW + 0x18) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma fwi_1c : kernel_text -∗ instr (mword_of_int (FW + 0x1c) : mword 64) false (ITYPE (mword_of_int 3498 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FW + 0x1c)%Z (mword_of_int 0xdaa50513 : mword 32)
    (mword_of_int (FW + 0x1c) : mword 64) (ITYPE (mword_of_int 3498 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fwdb_daa50513. Qed.

  Lemma fwi_20 : kernel_text -∗ instr (mword_of_int (FW + 0x20) : mword 64) false (JAL (mword_of_int 2094224 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FW + 0x20)%Z (mword_of_int 0xc90ff0ef : mword 32)
    (mword_of_int (FW + 0x20) : mword 64) (JAL (mword_of_int 2094224 : mword 21, Regidx (mword_of_int 1))) fwdb_c90ff0ef. Qed.

  (* --- the loop tail and its exit test -------------------------------- *)

  Lemma fwi_24 : kernel_text -∗ instr (mword_of_int (FW + 0x24) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (FW + 0x24)%Z (mword_of_int 0x04a1 : mword 16)
    (mword_of_int (FW + 0x24) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 8 : mword 6), Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) fwdc_04a1 exec_execute_C_ADDI. Qed.

  Lemma fwi_26 : kernel_text -∗ instr (mword_of_int (FW + 0x26) : mword 64) false (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (FW + 0x26)%Z (mword_of_int 0x03248163 : mword 32)
    (mword_of_int (FW + 0x26) : mword 64) (BTYPE (mword_of_int 34 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)) fwdb_03248163. Qed.

  (* --- the loop head: read the PTE and classify it --------------------- *)

  Lemma fwi_2a : kernel_text -∗ instr (mword_of_int (FW + 0x2a) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (FW + 0x2a)%Z (mword_of_int 0x609c : mword 16)
    (mword_of_int (FW + 0x2a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) fwdc_609c exec_execute_C_LD. Qed.

  Lemma fwi_2c : kernel_text -∗ instr (mword_of_int (FW + 0x2c) : mword 64) false (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_base (FW + 0x2c)%Z (mword_of_int 0x0017f713 : mword 32)
    (mword_of_int (FW + 0x2c) : mword 64) (ITYPE (mword_of_int 1 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)) fwdb_0017f713. Qed.

  Lemma fwi_30 : kernel_text -∗ instr (mword_of_int (FW + 0x30) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 250 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)).
  Proof. mk_rvc (FW + 0x30)%Z (mword_of_int 0xdb75 : mword 16)
    (mword_of_int (FW + 0x30) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 250 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BEQ)) fwdc_db75 exec_execute_C_BEQZ. Qed.

  Lemma fwi_32 : kernel_text -∗ instr (mword_of_int (FW + 0x32) : mword 64) false (ITYPE (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)).
  Proof. mk_base (FW + 0x32)%Z (mword_of_int 0x00e7f713 : mword 32)
    (mword_of_int (FW + 0x32) : mword 64) (ITYPE (mword_of_int 14 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), ANDI)) fwdb_00e7f713. Qed.

  Lemma fwi_36 : kernel_text -∗ instr (mword_of_int (FW + 0x36) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 241 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)).
  Proof. mk_rvc (FW + 0x36)%Z (mword_of_int 0xf36d : mword 16)
    (mword_of_int (FW + 0x36) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 241 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 6)), BNE)) fwdc_f36d exec_execute_C_BNEZ. Qed.

  (* --- the interior arm: PTE2PA, recurse, clear the entry -------------- *)

  Lemma fwi_38 : kernel_text -∗ instr (mword_of_int (FW + 0x38) : mword 64) true (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)).
  Proof. mk_rvc (FW + 0x38)%Z (mword_of_int 0x83a9 : mword 16)
    (mword_of_int (FW + 0x38) : mword 64) (SHIFTIOP (mword_of_int 10 : mword 6, creg2reg_idx (Cregidx (mword_of_int 7)), creg2reg_idx (Cregidx (mword_of_int 7)), SRLI)) cdec_83a9 exec_execute_C_SRLI. Qed.

  Lemma fwi_3a : kernel_text -∗ instr (mword_of_int (FW + 0x3a) : mword 64) false (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)).
  Proof. mk_base (FW + 0x3a)%Z (mword_of_int 0x00c79513 : mword 32)
    (mword_of_int (FW + 0x3a) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 10), SLLI)) bdec_00c79513. Qed.

  Lemma fwi_3e : kernel_text -∗ instr (mword_of_int (FW + 0x3e) : mword 64) false (JAL (mword_of_int 2097090 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FW + 0x3e)%Z (mword_of_int 0xfc3ff0ef : mword 32)
    (mword_of_int (FW + 0x3e) : mword 64) (JAL (mword_of_int 2097090 : mword 21, Regidx (mword_of_int 1))) fwdb_fc3ff0ef. Qed.

  Lemma fwi_42 : kernel_text -∗ instr (mword_of_int (FW + 0x42) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)).
  Proof. mk_base (FW + 0x42)%Z (mword_of_int 0x0004b023 : mword 32)
    (mword_of_int (FW + 0x42) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 9), 8)) fwdb_0004b023. Qed.

  Lemma fwi_46 : kernel_text -∗ instr (mword_of_int (FW + 0x46) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FW + 0x46)%Z (mword_of_int 0xbff9 : mword 16)
    (mword_of_int (FW + 0x46) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2031 : mword 11) ('b"0")), zreg)) cdec_bff9 exec_execute_C_J. Qed.

  (* --- the exit: kfree(pagetable), then the epilogue ------------------- *)

  Lemma fwi_48 : kernel_text -∗ instr (mword_of_int (FW + 0x48) : mword 64) true (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (FW + 0x48)%Z (mword_of_int 0x854e : mword 16)
    (mword_of_int (FW + 0x48) : mword 64) (RTYPE (Regidx (mword_of_int 19), zreg, Regidx (mword_of_int 10), ADD)) fwdc_854e exec_execute_C_MV. Qed.

  Lemma fwi_4a : kernel_text -∗ instr (mword_of_int (FW + 0x4a) : mword 64) false (JAL (mword_of_int 2094726 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FW + 0x4a)%Z (mword_of_int 0xe86ff0ef : mword 32)
    (mword_of_int (FW + 0x4a) : mword 64) (JAL (mword_of_int 2094726 : mword 21, Regidx (mword_of_int 1))) fwdb_e86ff0ef. Qed.

  Lemma fwi_4e : kernel_text -∗ instr (mword_of_int (FW + 0x4e) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FW + 0x4e)%Z (mword_of_int 0x70a2 : mword 16)
    (mword_of_int (FW + 0x4e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_70a2 exec_execute_C_LDSP. Qed.

  Lemma fwi_50 : kernel_text -∗ instr (mword_of_int (FW + 0x50) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FW + 0x50)%Z (mword_of_int 0x7402 : mword 16)
    (mword_of_int (FW + 0x50) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_7402 exec_execute_C_LDSP. Qed.

  Lemma fwi_52 : kernel_text -∗ instr (mword_of_int (FW + 0x52) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FW + 0x52)%Z (mword_of_int 0x64e2 : mword 16)
    (mword_of_int (FW + 0x52) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64e2 exec_execute_C_LDSP. Qed.

  Lemma fwi_54 : kernel_text -∗ instr (mword_of_int (FW + 0x54) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (FW + 0x54)%Z (mword_of_int 0x6942 : mword 16)
    (mword_of_int (FW + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6942 exec_execute_C_LDSP. Qed.

  Lemma fwi_56 : kernel_text -∗ instr (mword_of_int (FW + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (FW + 0x56)%Z (mword_of_int 0x69a2 : mword 16)
    (mword_of_int (FW + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 19), false, 8)) cdec_69a2 exec_execute_C_LDSP. Qed.

  Lemma fwi_58 : kernel_text -∗ instr (mword_of_int (FW + 0x58) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FW + 0x58)%Z (mword_of_int 0x6145 : mword 16)
    (mword_of_int (FW + 0x58) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 3 : mword 6), sp, sp, ADDI)) cdec_6145 exec_execute_C_ADDI16SP. Qed.

  Lemma fwi_5a : kernel_text -∗ instr (mword_of_int (FW + 0x5a) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FW + 0x5a)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FW + 0x5a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End FreewalkInstrs.

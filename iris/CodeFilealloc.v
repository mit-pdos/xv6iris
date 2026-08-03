(* CodeFilealloc.v -- the instruction-DECODE layer for xv6's filealloc().
   For EVERY instruction of

     filealloc @ 0x80003fb8 .. 0x80004014   (offsets 0x00 .. 0x5c)

   it proves a [kernel_text -* instr pc <is_rvc> <AST>] fact ([fai_<off>]) plus
   the per-instruction decode facts they consume.  Same shape as
   CodeKalloc / CodeFreerange: [mk_rvc] for compressed instructions,
   [mk_base] for 4-byte ones, with [mk_rvc]'s decode/expansion pair naming a
   [exec (ext_decode_compressed w) s = Some (<compressed AST>, s)] fact and the
   [exec (execute <compressed AST>) s = Some (ExecuteAs <base AST>, s)] one.

   filealloc's prologue and epilogue are the STANDARD 32-byte frame words, and
   c.li a5,1 / c.mv a0,s1 are shared too, so those decodes come from
   KernelRvcDecode's bit-keyed [cdec_<word>] base rather than being cloned
   here.  Only the five words nothing else uses are local, and they keep the
   same bit-keyed naming.

   Body (all addresses from the tracked KernelInstrs.v, never kernel.asm):

     0x00 1101       c.addi sp,sp,-32
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 1000       c.addi4spn s0,sp,32
     0x0a 0001e517   auipc a0,0x1e
     0x0e 49e50513   addi  a0,a0,1182     # a0 := &ftable
     0x12 c3ffc0ef   jal   ra,acquire
     0x16 0001e497   auipc s1,0x1e
     0x1a 4aa48493   addi  s1,s1,1194     # s1 := &ftable.file[0]  (the cursor)
     0x1e 0001f717   auipc a4,0x1f
     0x22 44270713   addi  a4,a4,1090     # a4 := &ftable.file[NFILE]  (= &disk)
     0x26 40dc       c.lw  a5,4(s1)       # f->ref                 <- LOOP HEAD
     0x28 cf89       c.beqz a5,+0x1a      # -> 0x42, found a free slot
     0x2a 02848493   addi  s1,s1,40       # f++
     0x2e fee49ce3   bne   s1,a4,-0x8     # -> 0x26, keep scanning
     0x32 0001e517   auipc a0,0x1e
     0x36 47650513   addi  a0,a0,1142     # a0 := &ftable
     0x3a c9ffc0ef   jal   ra,release
     0x3e 4481       c.li  s1,0           # table full: return 0
     0x40 a809       c.j   +0x12          # -> 0x52
     0x42 4785       c.li  a5,1                                    <- FOUND
     0x44 c0dc       c.sw  a5,4(s1)       # f->ref = 1
     0x46 0001e517   auipc a0,0x1e
     0x4a 46250513   addi  a0,a0,1122     # a0 := &ftable
     0x4e c8bfc0ef   jal   ra,release
     0x52 8526       c.mv  a0,s1          # return f (or 0)
     0x54 60e2       c.ldsp ra,24(sp)
     0x56 6442       c.ldsp s0,16(sp)
     0x58 64a2       c.ldsp s1,8(sp)
     0x5a 6105       c.addi16sp sp,32
     0x5c 8082       c.ret                                                    *)
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
Require Import KernelBaseDecode.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts for the words no other function uses.  Anything *)
(* a second proof ever needs should move to KernelRvcDecode as cdec_<word>. *)
(* ===================================================================== *)

(* +0x28  0xcf89  c.beqz a5,+0x1a *)
Lemma fadc_cf89 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xcf89 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 13, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.



(* ===================================================================== *)
(* Base (4-byte) decode facts.                                            *)
(* ===================================================================== *)

Lemma fadb_0001f717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0001f717 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x1f : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_49e50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x49e50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x49e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_47650513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x47650513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x476 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_46250513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x46250513 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x462 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_4aa48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x4aa48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x4aa : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_44270713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x44270713 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_02848493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02848493 : mword 32)) s
  = Some (ITYPE (mword_of_int 0x028 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* the two call sites and the back edge.  Branch/jump immediates are the
   decoder's POSITIVE RESIDUE of the (negative) byte displacement. *)
Lemma fadb_c3ffc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc3ffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fcc3e : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_c9ffc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc9ffc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fcc9e : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_c8bfc0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc8bfc0ef : mword 32)) s
  = Some (JAL (mword_of_int 0x1fcc8a : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma fadb_fee49ce3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfee49ce3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  The per-instruction [instr] facts.                                    *)
(* ===================================================================== *)
Section FileallocInstrs.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation FA := KernelSyms.filealloc.

  (* ---- prologue (the standard 32-byte frame) ---- *)

  Lemma fai_00 : kernel_text -∗ instr (mword_of_int (FA + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (FA + 0x00)%Z (mword_of_int 0x1101 : mword 16)
    (mword_of_int (FA + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma fai_02 : kernel_text -∗ instr (mword_of_int (FA + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (FA + 0x02)%Z (mword_of_int 0xec06 : mword 16)
    (mword_of_int (FA + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma fai_04 : kernel_text -∗ instr (mword_of_int (FA + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (FA + 0x04)%Z (mword_of_int 0xe822 : mword 16)
    (mword_of_int (FA + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma fai_06 : kernel_text -∗ instr (mword_of_int (FA + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (FA + 0x06)%Z (mword_of_int 0xe426 : mword 16)
    (mword_of_int (FA + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma fai_08 : kernel_text -∗ instr (mword_of_int (FA + 0x08) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (FA + 0x08)%Z (mword_of_int 0x1000 : mword 16)
    (mword_of_int (FA + 0x08) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  (* ---- a0 := &ftable ; acquire ---- *)

  Lemma fai_0a : kernel_text -∗ instr (mword_of_int (FA + 0x0a) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FA + 0x0a)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FA + 0x0a) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fai_0e : kernel_text -∗ instr (mword_of_int (FA + 0x0e) : mword 64) false (ITYPE (mword_of_int 0x49e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FA + 0x0e)%Z (mword_of_int 0x49e50513 : mword 32)
    (mword_of_int (FA + 0x0e) : mword 64) (ITYPE (mword_of_int 0x49e : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fadb_49e50513. Qed.

  Lemma fai_12 : kernel_text -∗ instr (mword_of_int (FA + 0x12) : mword 64) false (JAL (mword_of_int 0x1fcc3e : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FA + 0x12)%Z (mword_of_int 0xc3ffc0ef : mword 32)
    (mword_of_int (FA + 0x12) : mword 64) (JAL (mword_of_int 0x1fcc3e : mword 21, Regidx (mword_of_int 1))) fadb_c3ffc0ef. Qed.

  (* ---- s1 := &ftable.file[0] ; a4 := one past the last entry ---- *)

  Lemma fai_16 : kernel_text -∗ instr (mword_of_int (FA + 0x16) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (FA + 0x16)%Z (mword_of_int 0x0001e497 : mword 32)
    (mword_of_int (FA + 0x16) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_0001e497. Qed.

  Lemma fai_1a : kernel_text -∗ instr (mword_of_int (FA + 0x1a) : mword 64) false (ITYPE (mword_of_int 0x4aa : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (FA + 0x1a)%Z (mword_of_int 0x4aa48493 : mword 32)
    (mword_of_int (FA + 0x1a) : mword 64) (ITYPE (mword_of_int 0x4aa : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) fadb_4aa48493. Qed.

  Lemma fai_1e : kernel_text -∗ instr (mword_of_int (FA + 0x1e) : mword 64) false (UTYPE (mword_of_int 0x1f : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (FA + 0x1e)%Z (mword_of_int 0x0001f717 : mword 32)
    (mword_of_int (FA + 0x1e) : mword 64) (UTYPE (mword_of_int 0x1f : mword 20, Regidx (mword_of_int 14), AUIPC)) fadb_0001f717. Qed.

  Lemma fai_22 : kernel_text -∗ instr (mword_of_int (FA + 0x22) : mword 64) false (ITYPE (mword_of_int 0x442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (FA + 0x22)%Z (mword_of_int 0x44270713 : mword 32)
    (mword_of_int (FA + 0x22) : mword 64) (ITYPE (mword_of_int 0x442 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) fadb_44270713. Qed.

  (* ---- the scan loop ---- *)

  Lemma fai_26 : kernel_text -∗ instr (mword_of_int (FA + 0x26) : mword 64) true (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (FA + 0x26)%Z (mword_of_int 0x40dc : mword 16)
    (mword_of_int (FA + 0x26) : mword 64) (LOAD (mword_of_int 4, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_40dc cexec_40dc. Qed.

  Lemma fai_28 : kernel_text -∗ instr (mword_of_int (FA + 0x28) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 15), BEQ)).
  Proof. mk_rvc (FA + 0x28)%Z (mword_of_int 0xcf89 : mword 16)
    (mword_of_int (FA + 0x28) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 13 : mword 8) ('b"0")), zreg, Regidx (mword_of_int 15), BEQ)) fadc_cf89 exec_execute_C_BEQZ. Qed.

  Lemma fai_2a : kernel_text -∗ instr (mword_of_int (FA + 0x2a) : mword 64) false (ITYPE (mword_of_int 0x028 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (FA + 0x2a)%Z (mword_of_int 0x02848493 : mword 32)
    (mword_of_int (FA + 0x2a) : mword 64) (ITYPE (mword_of_int 0x028 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) fadb_02848493. Qed.

  Lemma fai_2e : kernel_text -∗ instr (mword_of_int (FA + 0x2e) : mword 64) false (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE)).
  Proof. mk_base (FA + 0x2e)%Z (mword_of_int 0xfee49ce3 : mword 32)
    (mword_of_int (FA + 0x2e) : mword 64) (BTYPE (mword_of_int 8184 : mword 13, Regidx (mword_of_int 14), Regidx (mword_of_int 9), BNE)) fadb_fee49ce3. Qed.

  (* ---- table-full arm: release, return 0 ---- *)

  Lemma fai_32 : kernel_text -∗ instr (mword_of_int (FA + 0x32) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FA + 0x32)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FA + 0x32) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fai_36 : kernel_text -∗ instr (mword_of_int (FA + 0x36) : mword 64) false (ITYPE (mword_of_int 0x476 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FA + 0x36)%Z (mword_of_int 0x47650513 : mword 32)
    (mword_of_int (FA + 0x36) : mword 64) (ITYPE (mword_of_int 0x476 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fadb_47650513. Qed.

  Lemma fai_3a : kernel_text -∗ instr (mword_of_int (FA + 0x3a) : mword 64) false (JAL (mword_of_int 0x1fcc9e : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FA + 0x3a)%Z (mword_of_int 0xc9ffc0ef : mword 32)
    (mword_of_int (FA + 0x3a) : mword 64) (JAL (mword_of_int 0x1fcc9e : mword 21, Regidx (mword_of_int 1))) fadb_c9ffc0ef. Qed.

  Lemma fai_3e : kernel_text -∗ instr (mword_of_int (FA + 0x3e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)).
  Proof. mk_rvc (FA + 0x3e)%Z (mword_of_int 0x4481 : mword 16)
    (mword_of_int (FA + 0x3e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 9), ADDI)) cdec_4481 exec_execute_C_LI. Qed.

  Lemma fai_40 : kernel_text -∗ instr (mword_of_int (FA + 0x40) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (FA + 0x40)%Z (mword_of_int 0xa809 : mword 16)
    (mword_of_int (FA + 0x40) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 9 : mword 11) ('b"0")), zreg)) cdec_a809 exec_execute_C_J. Qed.

  (* ---- found arm: f->ref = 1, release, return f ---- *)

  Lemma fai_42 : kernel_text -∗ instr (mword_of_int (FA + 0x42) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (FA + 0x42)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (FA + 0x42) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma fai_44 : kernel_text -∗ instr (mword_of_int (FA + 0x44) : mword 64) true (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)).
  Proof. mk_rvc (FA + 0x44)%Z (mword_of_int 0xc0dc : mword 16)
    (mword_of_int (FA + 0x44) : mword 64) (STORE (mword_of_int 4, Regidx (mword_of_int 15), Regidx (mword_of_int 9), 4)) cdec_c0dc cexec_c0dc. Qed.

  Lemma fai_46 : kernel_text -∗ instr (mword_of_int (FA + 0x46) : mword 64) false (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (FA + 0x46)%Z (mword_of_int 0x0001e517 : mword 32)
    (mword_of_int (FA + 0x46) : mword 64) (UTYPE (mword_of_int 0x1e : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_0001e517. Qed.

  Lemma fai_4a : kernel_text -∗ instr (mword_of_int (FA + 0x4a) : mword 64) false (ITYPE (mword_of_int 0x462 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (FA + 0x4a)%Z (mword_of_int 0x46250513 : mword 32)
    (mword_of_int (FA + 0x4a) : mword 64) (ITYPE (mword_of_int 0x462 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) fadb_46250513. Qed.

  Lemma fai_4e : kernel_text -∗ instr (mword_of_int (FA + 0x4e) : mword 64) false (JAL (mword_of_int 0x1fcc8a : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (FA + 0x4e)%Z (mword_of_int 0xc8bfc0ef : mword 32)
    (mword_of_int (FA + 0x4e) : mword 64) (JAL (mword_of_int 0x1fcc8a : mword 21, Regidx (mword_of_int 1))) fadb_c8bfc0ef. Qed.

  (* ---- join point + epilogue ---- *)

  Lemma fai_52 : kernel_text -∗ instr (mword_of_int (FA + 0x52) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (FA + 0x52)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (FA + 0x52) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma fai_54 : kernel_text -∗ instr (mword_of_int (FA + 0x54) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (FA + 0x54)%Z (mword_of_int 0x60e2 : mword 16)
    (mword_of_int (FA + 0x54) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma fai_56 : kernel_text -∗ instr (mword_of_int (FA + 0x56) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (FA + 0x56)%Z (mword_of_int 0x6442 : mword 16)
    (mword_of_int (FA + 0x56) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma fai_58 : kernel_text -∗ instr (mword_of_int (FA + 0x58) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (FA + 0x58)%Z (mword_of_int 0x64a2 : mword 16)
    (mword_of_int (FA + 0x58) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma fai_5a : kernel_text -∗ instr (mword_of_int (FA + 0x5a) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (FA + 0x5a)%Z (mword_of_int 0x6105 : mword 16)
    (mword_of_int (FA + 0x5a) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), sp, sp, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma fai_5c : kernel_text -∗ instr (mword_of_int (FA + 0x5c) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (FA + 0x5c)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (FA + 0x5c) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End FileallocInstrs.

(* CodeProcFreepagetable.v -- the instruction-DECODE layer for xv6's
   proc_freepagetable().

     proc_freepagetable @ 0x80001a92 .. 0x80001ad7   (offsets 0x00 .. 0x44, 30 in all)

   For EVERY instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([pfi_<off>]) plus the per-instruction decode facts they consume --
   [mk_rvc] for the compressed words, [mk_base] for the five 4-byte ones.
   Words the rest of the tree already decodes come from KernelRvcDecode /
   KernelBaseDecode; this function's own words are local, named
   [pfdc_<word>] (compressed) / [pfdb_<word>] (base).

   ALL TWENTY-ONE compressed words are in KernelRvcDecode: this is the
   plainest function shape in the kernel -- a 32-byte four-slot frame, two
   saved argument registers, three calls, and the mirror-image epilogue.
   ([c.li a3,0] was this function's only new one, and proc_pagetable's
   second failure tail wanted it too, so it was promoted there.)

   Body (all instruction bytes read out of the tracked KernelInstrs.v, never
   kernel.asm; the C is kernel/proc.c's
   proc_freepagetable(pagetable_t pagetable, uint64 sz)):

     0x00 1101       c.addi16sp sp,-32     # 32-byte frame (4 slots)
     0x02 ec06       c.sdsp ra,24(sp)
     0x04 e822       c.sdsp s0,16(sp)
     0x06 e426       c.sdsp s1,8(sp)
     0x08 e04a       c.sdsp s2,0(sp)
     0x0a 1000       c.addi4spn s0,sp,32
     0x0c 84aa       c.mv   s1,a0          # s1 := pagetable
     0x0e 892e       c.mv   s2,a1          # s2 := sz
     0x10 4681       c.li   a3,0           # do_free = 0
     0x12 4605       c.li   a2,1           # npages = 1
     0x14 040005b7   lui    a1,0x4000      # --- TRAMPOLINE = 2^38 - 4096:
     0x18 15fd       c.addi a1,a1,-1       #     (0x4000000 - 1) = 0x3ffffff
     0x1a 05b2       c.slli a1,a1,0xc      #     << 12  = 0x3ffffff000
     0x1c f50ff0ef   jal    ra,uvmunmap    # 0x800011fe -- a0 still holds the
                                           # pagetable, never reloaded
     0x20 4681       c.li   a3,0           # do_free = 0
     0x22 4605       c.li   a2,1           # npages = 1
     0x24 020005b7   lui    a1,0x2000      # --- TRAPFRAME = 2^38 - 8192:
     0x28 15fd       c.addi a1,a1,-1       #     (0x2000000 - 1) = 0x1ffffff
     0x2a 05b6       c.slli a1,a1,0xd      #     << 13  = 0x3fffffe000
     0x2c 8526       c.mv   a0,s1          # a0 := pagetable (uvmunmap clobbers)
     0x2e f3eff0ef   jal    ra,uvmunmap    # 0x800011fe
     0x32 85ca       c.mv   a1,s2          # a1 := sz
     0x34 8526       c.mv   a0,s1          # a0 := pagetable
     0x36 90bff0ef   jal    ra,uvmfree     # 0x800013d2
     0x3a 60e2       c.ldsp ra,24(sp)      # --- the epilogue
     0x3c 6442       c.ldsp s0,16(sp)
     0x3e 64a2       c.ldsp s1,8(sp)
     0x40 6902       c.ldsp s2,0(sp)
     0x42 6105       c.addi16sp sp,32
     0x44 8082       c.ret

   NO BRANCHES AT ALL -- there is no panic arm, no failure tail and no loop.
   The two [va] constants are built by lui/addi/slli rather than loaded, so
   the only arithmetic obligations are the two shift equalities showing that
   what lands in a1 IS TRAMPOLINE (resp. TRAPFRAME). *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecodeBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

Notation PF := KernelSyms.proc_freepagetable.

(* ---- this function's own decode words ---- *)

(* [cdec_4681] (c.li a3,0 -- do_free = 0, the whole point of both calls) is
   shared: proc_pagetable's second failure tail sets it too.  See
   KernelRvcDecode.v. *)

(* [bdec_040005b7] / [bdec_020005b7] (the two [lui]s) are shared -- see
   KernelBaseDecode.v.  The second was promoted there from a private copy in
   CodeProcPagetable.v, which builds the same two constants. *)

(* 0x1c  jal ra,uvmunmap  (offset -0x8b0) *)
Lemma pfdb_f50ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf50ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094928 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x2e  jal ra,uvmunmap  (offset -0x8c2) *)
Lemma pfdb_f3eff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xf3eff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094910 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* 0x36  jal ra,uvmfree  (offset -0x6f6) *)
Lemma pfdb_90bff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x90bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095370 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(*  THE PER-ADDRESS [instr] FACTS                                         *)
(* ===================================================================== *)

Section CodeProcFreepagetable.
  Context `{!riscvGS Σ}.

  Local Notation PFT off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (PF + off) : mword 64) rvc ast).

  Lemma pfi_00 : PFT 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).  (* c.addi16sp sp,-32 *)
  Proof. mk_rvc (PF + 0x00)%Z (mword_of_int 0x1101 : mword 16) (mword_of_int (PF + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 32 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1101 exec_execute_C_ADDI. Qed.

  Lemma pfi_02 : PFT 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).  (* c.sdsp ra,24(sp) *)
  Proof. mk_rvc (PF + 0x02)%Z (mword_of_int 0xec06 : mword 16) (mword_of_int (PF + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_ec06 exec_execute_C_SDSP. Qed.

  Lemma pfi_04 : PFT 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).  (* c.sdsp s0,16(sp) *)
  Proof. mk_rvc (PF + 0x04)%Z (mword_of_int 0xe822 : mword 16) (mword_of_int (PF + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e822 exec_execute_C_SDSP. Qed.

  Lemma pfi_06 : PFT 0x06 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).  (* c.sdsp s1,8(sp) *)
  Proof. mk_rvc (PF + 0x06)%Z (mword_of_int 0xe426 : mword 16) (mword_of_int (PF + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_e426 exec_execute_C_SDSP. Qed.

  Lemma pfi_08 : PFT 0x08 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).  (* c.sdsp s2,0(sp) *)
  Proof. mk_rvc (PF + 0x08)%Z (mword_of_int 0xe04a : mword 16) (mword_of_int (PF + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_e04a exec_execute_C_SDSP. Qed.

  Lemma pfi_0a : PFT 0x0a true (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).  (* c.addi4spn s0,sp,32 *)
  Proof. mk_rvc (PF + 0x0a)%Z (mword_of_int 0x1000 : mword 16) (mword_of_int (PF + 0x0a) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 8 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_1000 exec_execute_C_ADDI4SPN. Qed.

  Lemma pfi_0c : PFT 0x0c true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)).  (* c.mv s1,a0 *)
  Proof. mk_rvc (PF + 0x0c)%Z (mword_of_int 0x84aa : mword 16) (mword_of_int (PF + 0x0c) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 9), ADD)) cdec_84aa exec_execute_C_MV. Qed.

  Lemma pfi_0e : PFT 0x0e true (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)).  (* c.mv s2,a1 *)
  Proof. mk_rvc (PF + 0x0e)%Z (mword_of_int 0x892e : mword 16) (mword_of_int (PF + 0x0e) : mword 64) (RTYPE (Regidx (mword_of_int 11), zreg, Regidx (mword_of_int 18), ADD)) cdec_892e exec_execute_C_MV. Qed.

  Lemma pfi_10 : PFT 0x10 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).  (* c.li a3,0  -- do_free = 0 *)
  Proof. mk_rvc (PF + 0x10)%Z (mword_of_int 0x4681 : mword 16) (mword_of_int (PF + 0x10) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4681 exec_execute_C_LI. Qed.

  Lemma pfi_12 : PFT 0x12 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).  (* c.li a2,1  -- npages = 1 *)
  Proof. mk_rvc (PF + 0x12)%Z (mword_of_int 0x4605 : mword 16) (mword_of_int (PF + 0x12) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4605 exec_execute_C_LI. Qed.

  Lemma pfi_14 : PFT 0x14 false (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)).  (* lui a1,0x4000 *)
  Proof. mk_base (PF + 0x14)%Z (mword_of_int 0x040005b7 : mword 32) (mword_of_int (PF + 0x14) : mword 64) (UTYPE (mword_of_int 16384 : mword 20, Regidx (mword_of_int 11), LUI)) bdec_040005b7. Qed.

  Lemma pfi_18 : PFT 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).  (* c.addi a1,a1,-1 *)
  Proof. mk_rvc (PF + 0x18)%Z (mword_of_int 0x15fd : mword 16) (mword_of_int (PF + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) cdec_15fd exec_execute_C_ADDI. Qed.

  Lemma pfi_1a : PFT 0x1a true (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* c.slli a1,a1,0xc  -- a1 = TRAMPOLINE *)
  Proof. mk_rvc (PF + 0x1a)%Z (mword_of_int 0x05b2 : mword 16) (mword_of_int (PF + 0x1a) : mword 64) (SHIFTIOP (mword_of_int 12 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) cdec_05b2 exec_execute_C_SLLI. Qed.

  Lemma pfi_1c : PFT 0x1c false (JAL (mword_of_int 2094928 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,uvmunmap *)
  Proof. mk_base (PF + 0x1c)%Z (mword_of_int 0xf50ff0ef : mword 32) (mword_of_int (PF + 0x1c) : mword 64) (JAL (mword_of_int 2094928 : mword 21, Regidx (mword_of_int 1))) pfdb_f50ff0ef. Qed.

  Lemma pfi_20 : PFT 0x20 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)).  (* c.li a3,0  -- do_free = 0 *)
  Proof. mk_rvc (PF + 0x20)%Z (mword_of_int 0x4681 : mword 16) (mword_of_int (PF + 0x20) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 13), ADDI)) cdec_4681 exec_execute_C_LI. Qed.

  Lemma pfi_22 : PFT 0x22 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).  (* c.li a2,1  -- npages = 1 *)
  Proof. mk_rvc (PF + 0x22)%Z (mword_of_int 0x4605 : mword 16) (mword_of_int (PF + 0x22) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4605 exec_execute_C_LI. Qed.

  Lemma pfi_24 : PFT 0x24 false (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 11), LUI)).  (* lui a1,0x2000 *)
  Proof. mk_base (PF + 0x24)%Z (mword_of_int 0x020005b7 : mword 32) (mword_of_int (PF + 0x24) : mword 64) (UTYPE (mword_of_int 8192 : mword 20, Regidx (mword_of_int 11), LUI)) bdec_020005b7. Qed.

  Lemma pfi_28 : PFT 0x28 true (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)).  (* c.addi a1,a1,-1 *)
  Proof. mk_rvc (PF + 0x28)%Z (mword_of_int 0x15fd : mword 16) (mword_of_int (PF + 0x28) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 63 : mword 6), Regidx (mword_of_int 11), Regidx (mword_of_int 11), ADDI)) cdec_15fd exec_execute_C_ADDI. Qed.

  Lemma pfi_2a : PFT 0x2a true (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)).  (* c.slli a1,a1,0xd  -- a1 = TRAPFRAME *)
  Proof. mk_rvc (PF + 0x2a)%Z (mword_of_int 0x05b6 : mword 16) (mword_of_int (PF + 0x2a) : mword 64) (SHIFTIOP (mword_of_int 13 : mword 6, Regidx (mword_of_int 11), Regidx (mword_of_int 11), SLLI)) cdec_05b6 exec_execute_C_SLLI. Qed.

  Lemma pfi_2c : PFT 0x2c true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s1 *)
  Proof. mk_rvc (PF + 0x2c)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (PF + 0x2c) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pfi_2e : PFT 0x2e false (JAL (mword_of_int 2094910 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,uvmunmap *)
  Proof. mk_base (PF + 0x2e)%Z (mword_of_int 0xf3eff0ef : mword 32) (mword_of_int (PF + 0x2e) : mword 64) (JAL (mword_of_int 2094910 : mword 21, Regidx (mword_of_int 1))) pfdb_f3eff0ef. Qed.

  Lemma pfi_32 : PFT 0x32 true (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)).  (* c.mv a1,s2 *)
  Proof. mk_rvc (PF + 0x32)%Z (mword_of_int 0x85ca : mword 16) (mword_of_int (PF + 0x32) : mword 64) (RTYPE (Regidx (mword_of_int 18), zreg, Regidx (mword_of_int 11), ADD)) cdec_85ca exec_execute_C_MV. Qed.

  Lemma pfi_34 : PFT 0x34 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).  (* c.mv a0,s1 *)
  Proof. mk_rvc (PF + 0x34)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (PF + 0x34) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma pfi_36 : PFT 0x36 false (JAL (mword_of_int 2095370 : mword 21, Regidx (mword_of_int 1))).  (* jal ra,uvmfree *)
  Proof. mk_base (PF + 0x36)%Z (mword_of_int 0x90bff0ef : mword 32) (mword_of_int (PF + 0x36) : mword 64) (JAL (mword_of_int 2095370 : mword 21, Regidx (mword_of_int 1))) pfdb_90bff0ef. Qed.

  Lemma pfi_3a : PFT 0x3a true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).  (* c.ldsp ra,24(sp) *)
  Proof. mk_rvc (PF + 0x3a)%Z (mword_of_int 0x60e2 : mword 16) (mword_of_int (PF + 0x3a) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60e2 exec_execute_C_LDSP. Qed.

  Lemma pfi_3c : PFT 0x3c true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).  (* c.ldsp s0,16(sp) *)
  Proof. mk_rvc (PF + 0x3c)%Z (mword_of_int 0x6442 : mword 16) (mword_of_int (PF + 0x3c) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6442 exec_execute_C_LDSP. Qed.

  Lemma pfi_3e : PFT 0x3e true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)).  (* c.ldsp s1,8(sp) *)
  Proof. mk_rvc (PF + 0x3e)%Z (mword_of_int 0x64a2 : mword 16) (mword_of_int (PF + 0x3e) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 9), false, 8)) cdec_64a2 exec_execute_C_LDSP. Qed.

  Lemma pfi_40 : PFT 0x40 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)).  (* c.ldsp s2,0(sp) *)
  Proof. mk_rvc (PF + 0x40)%Z (mword_of_int 0x6902 : mword 16) (mword_of_int (PF + 0x40) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 18), false, 8)) cdec_6902 exec_execute_C_LDSP. Qed.

  Lemma pfi_42 : PFT 0x42 true (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).  (* c.addi16sp sp,32 *)
  Proof. mk_rvc (PF + 0x42)%Z (mword_of_int 0x6105 : mword 16) (mword_of_int (PF + 0x42) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 2 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_6105 exec_execute_C_ADDI16SP. Qed.

  Lemma pfi_44 : PFT 0x44 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).  (* c.ret *)
  Proof. mk_rvc (PF + 0x44)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (PF + 0x44) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.
End CodeProcFreepagetable.

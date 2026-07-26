(* WpInitlock.v -- whole-function S-mode WP for xv6's initlock().

     void initlock(struct spinlock *lk, char *name) {
       lk->name = name;   // c.sd  a1,8(a0)
       lk->locked = 0;    // sw    zero,0(a0)
       lk->cpu = 0;       // sd    zero,16(a0)
     }

   initlock @ 0x80000b88 (offsets +0x00 .. +0x18), 11 instructions:
     +0x00  1141      c.addi  sp,sp,-16
     +0x02  e406      c.sdsp  ra,8(sp)
     +0x04  e022      c.sdsp  s0,0(sp)
     +0x06  0800      c.addi4spn s0,sp,16
     +0x08  e50c      c.sd    a1,8(a0)      lk->name = name
     +0x0a  00052023  sw      zero,0(a0)    lk->locked = 0
     +0x0e  00053823  sd      zero,16(a0)   lk->cpu = 0
     +0x12  60a2      c.ldsp  ra,8(sp)
     +0x14  6402      c.ldsp  s0,0(sp)
     +0x16  0141      c.addi  sp,sp,16
     +0x18  8082      c.ret

   The function makes no sub-calls, holds ONE [smode_config] end-to-end, and
   never touches the interrupt-nesting state -- so its spec needs neither a
   ghost SIE half nor [intr_count].  It owns the spinlock's three struct fields
   (locked : 4B @ +0, name : 8B @ +8, cpu : 8B @ +16) as raw memory and hands
   them back initialised.  The [locked := 0] store is a plain 4-byte zero store
   over a PLAINLY-owned word (the lock is not yet an invariant) -- for that we
   build [wp_sw_zero_s], the width-4 sibling of [wp_sd_zero_s]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import SmodeCore.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Decode facts specific to initlock: the c.sd (CS-form) and the two      *)
(* 32-bit zero stores.  (The prologue/epilogue RVC decodes reuse the      *)
(* shared [cdec_*] from KernelRvcDecode.v.)                               *)
(* ===================================================================== *)
Lemma ildc_e50c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe50c : mword 16)) s
  = Some (C_SD (mword_of_int 1, Cregidx (mword_of_int 2), Cregidx (mword_of_int 3)), s).
Proof. intro H. rvc_oneshot s H. Qed.

Lemma ildb_00052023 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00052023 : mword 32)) s
  = Some (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4), s).
Proof. decode_bridge_ms. Qed.

Lemma ildb_00053823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00053823 : mword 32)) s
  = Some (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8), s).
Proof. decode_bridge_ms. Qed.

Section InitlockLeaf.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ===== the plain 4-byte zero store [sw zero, imm(rs1)] over a PLAINLY-  *)
  (*       owned word.  Width-4 sibling of [wp_sd_zero_s_r]; cloned from    *)
  (*       it with the width-8 store tower swapped for the width-4 one.     *)




End InitlockLeaf.

(* initlock's epilogue [c.addi sp,+16] undoes its prologue [c.addi sp,-16].
   (mword_of_int 48 : mword 6) is -16 in 6-bit two's complement. *)
Lemma initlock_sp_cancel (X : mword 64) :
  add_vec (add_vec X (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6))))
          (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6))) = X.
Proof.
  assert (add_vec_unsigned : forall x y : mword 64,
            bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
  { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
      SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
    rewrite bv_add_unsigned. reflexivity. }
  apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
  assert (HA : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)) : mword 64) = 18446744073709551600) by (vm_compute; reflexivity).
  assert (HB : bv_unsigned (sign_extend' 64 (sign_extend' 12 (mword_of_int 16 : mword 6)) : mword 64) = 16) by (vm_compute; reflexivity).
  rewrite HA HB. rewrite <- Z.add_assoc.
  replace (18446744073709551600 + 16) with (bv_modulus 64) by (vm_compute; reflexivity).
  rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
Qed.

Section Initlock.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Notation IL := KernelSyms.initlock.

  (* ===== instruction-DECODE facts (the [kernel_text -* instr] window) ===== *)
  Lemma ini_00 : kernel_text -∗ instr (mword_of_int (IL + 0x00) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IL + 0x00)%Z (mword_of_int 0x1141 : mword 16)
    (mword_of_int (IL + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma ini_02 : kernel_text -∗ instr (mword_of_int (IL + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (IL + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (IL + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma ini_04 : kernel_text -∗ instr (mword_of_int (IL + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (IL + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (IL + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma ini_06 : kernel_text -∗ instr (mword_of_int (IL + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (IL + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (IL + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  Lemma ini_08 : kernel_text -∗ instr (mword_of_int (IL + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)).
  Proof. mk_rvc (IL + 0x08)%Z (mword_of_int 0xe50c : mword 16)
    (mword_of_int (IL + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), creg2reg_idx (Cregidx (mword_of_int 3)), creg2reg_idx (Cregidx (mword_of_int 2)), 8)) ildc_e50c exec_execute_C_SD. Qed.

  Lemma ini_0a : kernel_text -∗ instr (mword_of_int (IL + 0x0a) : mword 64) false (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)).
  Proof. mk_base (IL + 0x0a)%Z (mword_of_int 0x00052023 : mword 32)
    (mword_of_int (IL + 0x0a) : mword 64) (STORE (mword_of_int 0 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 4)) ildb_00052023. Qed.

  Lemma ini_0e : kernel_text -∗ instr (mword_of_int (IL + 0x0e) : mword 64) false (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)).
  Proof. mk_base (IL + 0x0e)%Z (mword_of_int 0x00053823 : mword 32)
    (mword_of_int (IL + 0x0e) : mword 64) (STORE (mword_of_int 0x10 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 10), 8)) ildb_00053823. Qed.

  Lemma ini_12 : kernel_text -∗ instr (mword_of_int (IL + 0x12) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (IL + 0x12)%Z (mword_of_int 0x60a2 : mword 16)
    (mword_of_int (IL + 0x12) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma ini_14 : kernel_text -∗ instr (mword_of_int (IL + 0x14) : mword 64) true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (IL + 0x14)%Z (mword_of_int 0x6402 : mword 16)
    (mword_of_int (IL + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma ini_16 : kernel_text -∗ instr (mword_of_int (IL + 0x16) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IL + 0x16)%Z (mword_of_int 0x0141 : mword 16)
    (mword_of_int (IL + 0x16) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma ini_18 : kernel_text -∗ instr (mword_of_int (IL + 0x18) : mword 64) true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IL + 0x18)%Z (mword_of_int 0x8082 : mword 16)
    (mword_of_int (IL + 0x18) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* ============================================================= *)
  (* initlock: whole-function S-mode WP.  Owns the spinlock's three  *)
  (* struct fields as raw memory and returns them initialised;       *)
  (* makes no sub-calls (a pure prologue / three stores / epilogue). *)
  (* ============================================================= *)


End Initlock.

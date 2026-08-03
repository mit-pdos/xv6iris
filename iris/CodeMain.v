(* CodeMain.v -- the instruction-DECODE layer for xv6's main().

     main @ 0x80000e7e .. 0x80000f2f   (offsets 0x00 .. 0xb0)

   For every instruction it proves a [kernel_text -* instr pc <is_rvc> <AST>]
   fact ([mni_<off>]) plus the per-instruction decode facts they consume
   ([mndc_<word>] compressed / [mndb_<word>] base).

   main is a TWO-ARM function joined at its tail.  Layout (the offsets are
   what the proof's pc chain steps through):

     0x00 .. 0x06   the standard 16-byte / 2-slot frame (shared [cdec_*])
     0x08           jal cpuid
     0x0c .. 0x10   auipc a4 / addi a4 -> &started
     0x14           beqz a0, +0x2e     -- cpuid() == 0 ? boot arm : secondary
     ---- secondary arm ----
     0x16 .. 0x1a   the spin loop: lw a5,0(a4) / sext.w a5 / beqz a5, -4
     0x1c           fence rw,rw        (__atomic_thread_fence(SEQ_CST))
     0x20 .. 0x2e   printk("hart %d starting\n", cpuid())
     0x32 .. 0x3a   kvminithart / trapinithart / plicinithart
     0x3e           jal scheduler      -- THE JOIN POINT, and the exit
     ---- boot arm ----
     0x42 .. 0x9e   consoleinit .. userinit (the whole init sequence)
     0xa2           fence rw,rw
     0xa6 .. 0xac   li a5,1 / auipc a4 / sw a5,778(a4)   -- started = 1
     0xb0           j 0x3e             -- back to the join

   main NEVER RETURNS: there is no epilogue and no [jalr ra], so there is no
   [c.ldsp]/[c.addi16sp]/[c.jr] tail here -- 0xb0 is the last instruction.

   The fence rw,rw word and the three creg->reg conversions are SHARED
   ([KernelBaseDecode.bdec_0330000f], [KernelRvcDecode.creg_c{2,6,7}]) -- three
   functions decode that word and three name those conversions. *)
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
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import KernelRvcDecode KernelBaseDecode.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* Compressed decode facts unique to main.                                *)
(* ===================================================================== *)

(* 0xc51d  beqz a0,+0x2e  (the cpuid() == 0 test; imm[8:1] = 23) *)
Lemma mndc_c51d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xc51d : mword 16)) s
  = Some (C_BEQZ (mword_of_int 23, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x431c  lw a5,0(a4)  -- the [started] read *)
Lemma mndc_431c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x431c : mword 16)) s
  = Some (C_LW (mword_of_int 0, Cregidx (mword_of_int 6), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xdff5  beqz a5,-4  -- the spin loop's back edge (imm[8:1] = 254) *)
Lemma mndc_dff5 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xdff5 : mword 16)) s
  = Some (C_BEQZ (mword_of_int 254, Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x85aa  mv a1,a0  -- the cpuid() result becomes printk's vararg *)
Lemma mndc_85aa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x85aa : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 11), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0xb779  j -0x72  -- the boot arm's jump back to the [jal scheduler] join *)
Lemma mndc_b779 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb779 : mword 16)) s
  = Some (C_J (mword_of_int 1991), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Base (32-bit) decode facts unique to main.  Every immediate here is    *)
(* POSITIVE in the image, so the JAL displacements toward a LOWER address *)
(* appear as their 21-bit positive residue (-2480 -> 2094672, ...).       *)
(* ===================================================================== *)

(* auipc a4,0x9 -- the high half of &started, used on BOTH arms *)
Lemma mndb_00009717 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00009717 : mword 32)) s
  = Some (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 14), AUIPC), s).
Proof. decode_bridge_ms. Qed.

(* addi a4,a4,934 -- a4 := &started *)
Lemma mndb_3a670713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x3a670713 : mword 32)) s
  = Some (ITYPE (mword_of_int 934 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* the four format-string materializations: addi a0,a0,<off> off &etext *)
Lemma mndb_1f450513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1f450513 : mword 32)) s
  = Some (ITYPE (mword_of_int 500 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_1b050513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1b050513 : mword 32)) s
  = Some (ITYPE (mword_of_int 432 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_1ac50513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x1ac50513 : mword 32)) s
  = Some (ITYPE (mword_of_int 428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_19850513 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x19850513 : mword 32)) s
  = Some (ITYPE (mword_of_int 408 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI), s).
Proof. decode_bridge_ms. Qed.

(* sw a5,778(a4) -- started = 1 *)
Lemma mndb_30f72523 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x30f72523 : mword 32)) s
  = Some (STORE (mword_of_int 778 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4), s).
Proof. decode_bridge_ms. Qed.

(* ---- the 22 jal displacements, in image order ---- *)

Lemma mndb_24b000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* cpuid *)
  exec (ext_decode (mword_of_int 0x24b000ef : mword 32)) s
  = Some (JAL (mword_of_int 2634 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_233000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* cpuid *)
  exec (ext_decode (mword_of_int 0x233000ef : mword 32)) s
  = Some (JAL (mword_of_int 2610 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_e50ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* printk *)
  exec (ext_decode (mword_of_int 0xe50ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094672 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_080000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* kvminithart *)
  exec (ext_decode (mword_of_int 0x080000ef : mword 32)) s
  = Some (JAL (mword_of_int 128 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_572010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* trapinithart *)
  exec (ext_decode (mword_of_int 0x572010ef : mword 32)) s
  = Some (JAL (mword_of_int 5490 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_5e0040ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* plicinithart *)
  exec (ext_decode (mword_of_int 0x5e0040ef : mword 32)) s
  = Some (JAL (mword_of_int 17888 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_6bf000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* scheduler *)
  exec (ext_decode (mword_of_int 0x6bf000ef : mword 32)) s
  = Some (JAL (mword_of_int 3774 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_d62ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* consoleinit *)
  exec (ext_decode (mword_of_int 0xd62ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094434 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_99fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* printkinit *)
  exec (ext_decode (mword_of_int 0x99fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095518 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_e2cff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* printk *)
  exec (ext_decode (mword_of_int 0xe2cff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_e20ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* printk *)
  exec (ext_decode (mword_of_int 0xe20ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094624 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_e14ff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* printk *)
  exec (ext_decode (mword_of_int 0xe14ff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2094612 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_c0fff0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* kinit *)
  exec (ext_decode (mword_of_int 0xc0fff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2096142 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_2cc000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* kvminit *)
  exec (ext_decode (mword_of_int 0x2cc000ef : mword 32)) s
  = Some (JAL (mword_of_int 716 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_03c000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* kvminithart *)
  exec (ext_decode (mword_of_int 0x03c000ef : mword 32)) s
  = Some (JAL (mword_of_int 60 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_123000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* procinit *)
  exec (ext_decode (mword_of_int 0x123000ef : mword 32)) s
  = Some (JAL (mword_of_int 2338 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_506010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* trapinit *)
  exec (ext_decode (mword_of_int 0x506010ef : mword 32)) s
  = Some (JAL (mword_of_int 5382 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_526010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* trapinithart *)
  exec (ext_decode (mword_of_int 0x526010ef : mword 32)) s
  = Some (JAL (mword_of_int 5414 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_57a040ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* plicinit *)
  exec (ext_decode (mword_of_int 0x57a040ef : mword 32)) s
  = Some (JAL (mword_of_int 17786 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_590040ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* plicinithart *)
  exec (ext_decode (mword_of_int 0x590040ef : mword 32)) s
  = Some (JAL (mword_of_int 17808 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_3a5010ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* binit *)
  exec (ext_decode (mword_of_int 0x3a5010ef : mword 32)) s
  = Some (JAL (mword_of_int 7076 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_0f6020ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* iinit *)
  exec (ext_decode (mword_of_int 0x0f6020ef : mword 32)) s
  = Some (JAL (mword_of_int 8438 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_080030ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* fileinit *)
  exec (ext_decode (mword_of_int 0x080030ef : mword 32)) s
  = Some (JAL (mword_of_int 12416 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_670040ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* virtio_disk_init *)
  exec (ext_decode (mword_of_int 0x670040ef : mword 32)) s
  = Some (JAL (mword_of_int 18032 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

Lemma mndb_4b3000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->  (* userinit *)
  exec (ext_decode (mword_of_int 0x4b3000ef : mword 32)) s
  = Some (JAL (mword_of_int 3250 : mword 21, Regidx (mword_of_int 1)), s).
Proof. decode_bridge_ms. Qed.

(* ===================================================================== *)
(* The c.lw AST bridge: the RVC expansion yields a [creg2reg_idx] pair and *)
(* a [zero_extend'] of the scaled 5-bit offset, while [wp_load_s_sconf_au] *)
(* wants plain [Regidx]es and a 12-bit immediate.  Both forms are          *)
(* convertible, so the bridge is three [vm_compute] equations rewritten    *)
(* into the goal before [mk_rvc] runs -- done HERE so main's proof only    *)
(* ever sees the leaf's shape.  (The two BEQZ facts KEEP the              *)
(* [creg2reg_idx] form: that is exactly what [wp_cbeqz_*_s_sconf] takes,   *)
(* with the bridge as its own premise.)                                    *)
(* ===================================================================== *)

Lemma mnd_clw_imm0 :
  zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")) = (mword_of_int 0 : mword 12).
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Section CodeMain.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Notation MN := KernelSyms.main.

  (* ---- prologue: 2-slot frame push, save ra/s0, set up s0 ---- *)

  Lemma mni_00 : kernel_text -∗ instr (mword_of_int MN : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc MN (mword_of_int 0x1141 : mword 16)
    (mword_of_int MN : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma mni_02 : kernel_text -∗ instr (mword_of_int (MN + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (MN + 0x02)%Z (mword_of_int 0xe406 : mword 16)
    (mword_of_int (MN + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma mni_04 : kernel_text -∗ instr (mword_of_int (MN + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (MN + 0x04)%Z (mword_of_int 0xe022 : mword 16)
    (mword_of_int (MN + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma mni_06 : kernel_text -∗ instr (mword_of_int (MN + 0x06) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (MN + 0x06)%Z (mword_of_int 0x0800 : mword 16)
    (mword_of_int (MN + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- cpuid(); a4 := &started; branch on the result ---- *)

  Lemma mni_08 : kernel_text -∗ instr (mword_of_int (MN + 0x08) : mword 64) false (JAL (mword_of_int 2634 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x08)%Z (mword_of_int 0x24b000ef : mword 32)
    (mword_of_int (MN + 0x08) : mword 64) (JAL (mword_of_int 2634 : mword 21, Regidx (mword_of_int 1))) mndb_24b000ef. Qed.

  Lemma mni_0c : kernel_text -∗ instr (mword_of_int (MN + 0x0c) : mword 64) false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (MN + 0x0c)%Z (mword_of_int 0x00009717 : mword 32)
    (mword_of_int (MN + 0x0c) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 14), AUIPC)) mndb_00009717. Qed.

  Lemma mni_10 : kernel_text -∗ instr (mword_of_int (MN + 0x10) : mword 64) false (ITYPE (mword_of_int 934 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (MN + 0x10)%Z (mword_of_int 0x3a670713 : mword 32)
    (mword_of_int (MN + 0x10) : mword 64) (ITYPE (mword_of_int 934 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) mndb_3a670713. Qed.

  Lemma mni_14 : kernel_text -∗ instr (mword_of_int (MN + 0x14) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (MN + 0x14)%Z (mword_of_int 0xc51d : mword 16)
    (mword_of_int (MN + 0x14) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 23 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) mndc_c51d exec_execute_C_BEQZ. Qed.

  (* ---- the secondary arm's spin loop: while (started == 0) ; ---- *)

  Lemma mni_16 : kernel_text -∗ instr (mword_of_int (MN + 0x16) : mword 64) true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 15), false, 4)).
  Proof.
    rewrite -mnd_clw_imm0 -creg_c6 -creg_c7.
    mk_rvc (MN + 0x16)%Z (mword_of_int 0x431c : mword 16)
      (mword_of_int (MN + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 6)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) mndc_431c exec_execute_C_LW.
  Qed.

  Lemma mni_18 : kernel_text -∗ instr (mword_of_int (MN + 0x18) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (MN + 0x18)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (MN + 0x18) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma mni_1a : kernel_text -∗ instr (mword_of_int (MN + 0x1a) : mword 64) true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 254 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)).
  Proof. mk_rvc (MN + 0x1a)%Z (mword_of_int 0xdff5 : mword 16)
    (mword_of_int (MN + 0x1a) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 254 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 7)), BEQ)) mndc_dff5 exec_execute_C_BEQZ. Qed.

  Lemma mni_1c : kernel_text -∗ instr (mword_of_int (MN + 0x1c) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (MN + 0x1c)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (MN + 0x1c) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  (* ---- printk("hart %d starting\n", cpuid()) ---- *)

  Lemma mni_20 : kernel_text -∗ instr (mword_of_int (MN + 0x20) : mword 64) false (JAL (mword_of_int 2610 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x20)%Z (mword_of_int 0x233000ef : mword 32)
    (mword_of_int (MN + 0x20) : mword 64) (JAL (mword_of_int 2610 : mword 21, Regidx (mword_of_int 1))) mndb_233000ef. Qed.

  Lemma mni_24 : kernel_text -∗ instr (mword_of_int (MN + 0x24) : mword 64) true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)).
  Proof. mk_rvc (MN + 0x24)%Z (mword_of_int 0x85aa : mword 16)
    (mword_of_int (MN + 0x24) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 11), ADD)) mndc_85aa exec_execute_C_MV. Qed.

  Lemma mni_26 : kernel_text -∗ instr (mword_of_int (MN + 0x26) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (MN + 0x26)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (MN + 0x26) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma mni_2a : kernel_text -∗ instr (mword_of_int (MN + 0x2a) : mword 64) false (ITYPE (mword_of_int 500 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (MN + 0x2a)%Z (mword_of_int 0x1f450513 : mword 32)
    (mword_of_int (MN + 0x2a) : mword 64) (ITYPE (mword_of_int 500 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mndb_1f450513. Qed.

  Lemma mni_2e : kernel_text -∗ instr (mword_of_int (MN + 0x2e) : mword 64) false (JAL (mword_of_int 2094672 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x2e)%Z (mword_of_int 0xe50ff0ef : mword 32)
    (mword_of_int (MN + 0x2e) : mword 64) (JAL (mword_of_int 2094672 : mword 21, Regidx (mword_of_int 1))) mndb_e50ff0ef. Qed.

  (* ---- the secondary arm's three per-hart initializers ---- *)

  Lemma mni_32 : kernel_text -∗ instr (mword_of_int (MN + 0x32) : mword 64) false (JAL (mword_of_int 128 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x32)%Z (mword_of_int 0x080000ef : mword 32)
    (mword_of_int (MN + 0x32) : mword 64) (JAL (mword_of_int 128 : mword 21, Regidx (mword_of_int 1))) mndb_080000ef. Qed.

  Lemma mni_36 : kernel_text -∗ instr (mword_of_int (MN + 0x36) : mword 64) false (JAL (mword_of_int 5490 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x36)%Z (mword_of_int 0x572010ef : mword 32)
    (mword_of_int (MN + 0x36) : mword 64) (JAL (mword_of_int 5490 : mword 21, Regidx (mword_of_int 1))) mndb_572010ef. Qed.

  Lemma mni_3a : kernel_text -∗ instr (mword_of_int (MN + 0x3a) : mword 64) false (JAL (mword_of_int 17888 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x3a)%Z (mword_of_int 0x5e0040ef : mword 32)
    (mword_of_int (MN + 0x3a) : mword 64) (JAL (mword_of_int 17888 : mword 21, Regidx (mword_of_int 1))) mndb_5e0040ef. Qed.

  (* ---- THE JOIN: jal scheduler.  main's exit; scheduler never returns. ---- *)

  Lemma mni_3e : kernel_text -∗ instr (mword_of_int (MN + 0x3e) : mword 64) false (JAL (mword_of_int 3774 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x3e)%Z (mword_of_int 0x6bf000ef : mword 32)
    (mword_of_int (MN + 0x3e) : mword 64) (JAL (mword_of_int 3774 : mword 21, Regidx (mword_of_int 1))) mndb_6bf000ef. Qed.

  (* ---- the boot arm: consoleinit(); printkinit() ---- *)

  Lemma mni_42 : kernel_text -∗ instr (mword_of_int (MN + 0x42) : mword 64) false (JAL (mword_of_int 2094434 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x42)%Z (mword_of_int 0xd62ff0ef : mword 32)
    (mword_of_int (MN + 0x42) : mword 64) (JAL (mword_of_int 2094434 : mword 21, Regidx (mword_of_int 1))) mndb_d62ff0ef. Qed.

  Lemma mni_46 : kernel_text -∗ instr (mword_of_int (MN + 0x46) : mword 64) false (JAL (mword_of_int 2095518 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x46)%Z (mword_of_int 0x99fff0ef : mword 32)
    (mword_of_int (MN + 0x46) : mword 64) (JAL (mword_of_int 2095518 : mword 21, Regidx (mword_of_int 1))) mndb_99fff0ef. Qed.

  (* ---- printk("\n"); printk("xv6 kernel is booting\n"); printk("\n") ---- *)

  Lemma mni_4a : kernel_text -∗ instr (mword_of_int (MN + 0x4a) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (MN + 0x4a)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (MN + 0x4a) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma mni_4e : kernel_text -∗ instr (mword_of_int (MN + 0x4e) : mword 64) false (ITYPE (mword_of_int 432 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (MN + 0x4e)%Z (mword_of_int 0x1b050513 : mword 32)
    (mword_of_int (MN + 0x4e) : mword 64) (ITYPE (mword_of_int 432 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mndb_1b050513. Qed.

  Lemma mni_52 : kernel_text -∗ instr (mword_of_int (MN + 0x52) : mword 64) false (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x52)%Z (mword_of_int 0xe2cff0ef : mword 32)
    (mword_of_int (MN + 0x52) : mword 64) (JAL (mword_of_int 2094636 : mword 21, Regidx (mword_of_int 1))) mndb_e2cff0ef. Qed.

  Lemma mni_56 : kernel_text -∗ instr (mword_of_int (MN + 0x56) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (MN + 0x56)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (MN + 0x56) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma mni_5a : kernel_text -∗ instr (mword_of_int (MN + 0x5a) : mword 64) false (ITYPE (mword_of_int 428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (MN + 0x5a)%Z (mword_of_int 0x1ac50513 : mword 32)
    (mword_of_int (MN + 0x5a) : mword 64) (ITYPE (mword_of_int 428 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mndb_1ac50513. Qed.

  Lemma mni_5e : kernel_text -∗ instr (mword_of_int (MN + 0x5e) : mword 64) false (JAL (mword_of_int 2094624 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x5e)%Z (mword_of_int 0xe20ff0ef : mword 32)
    (mword_of_int (MN + 0x5e) : mword 64) (JAL (mword_of_int 2094624 : mword 21, Regidx (mword_of_int 1))) mndb_e20ff0ef. Qed.

  Lemma mni_62 : kernel_text -∗ instr (mword_of_int (MN + 0x62) : mword 64) false (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)).
  Proof. mk_base (MN + 0x62)%Z (mword_of_int 0x00006517 : mword 32)
    (mword_of_int (MN + 0x62) : mword 64) (UTYPE (mword_of_int 6 : mword 20, Regidx (mword_of_int 10), AUIPC)) bdec_00006517. Qed.

  Lemma mni_66 : kernel_text -∗ instr (mword_of_int (MN + 0x66) : mword 64) false (ITYPE (mword_of_int 408 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)).
  Proof. mk_base (MN + 0x66)%Z (mword_of_int 0x19850513 : mword 32)
    (mword_of_int (MN + 0x66) : mword 64) (ITYPE (mword_of_int 408 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), ADDI)) mndb_19850513. Qed.

  Lemma mni_6a : kernel_text -∗ instr (mword_of_int (MN + 0x6a) : mword 64) false (JAL (mword_of_int 2094612 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x6a)%Z (mword_of_int 0xe14ff0ef : mword 32)
    (mword_of_int (MN + 0x6a) : mword 64) (JAL (mword_of_int 2094612 : mword 21, Regidx (mword_of_int 1))) mndb_e14ff0ef. Qed.

  (* ---- kinit(); kvminit(); kvminithart(); procinit() ---- *)

  Lemma mni_6e : kernel_text -∗ instr (mword_of_int (MN + 0x6e) : mword 64) false (JAL (mword_of_int 2096142 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x6e)%Z (mword_of_int 0xc0fff0ef : mword 32)
    (mword_of_int (MN + 0x6e) : mword 64) (JAL (mword_of_int 2096142 : mword 21, Regidx (mword_of_int 1))) mndb_c0fff0ef. Qed.

  Lemma mni_72 : kernel_text -∗ instr (mword_of_int (MN + 0x72) : mword 64) false (JAL (mword_of_int 716 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x72)%Z (mword_of_int 0x2cc000ef : mword 32)
    (mword_of_int (MN + 0x72) : mword 64) (JAL (mword_of_int 716 : mword 21, Regidx (mword_of_int 1))) mndb_2cc000ef. Qed.

  Lemma mni_76 : kernel_text -∗ instr (mword_of_int (MN + 0x76) : mword 64) false (JAL (mword_of_int 60 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x76)%Z (mword_of_int 0x03c000ef : mword 32)
    (mword_of_int (MN + 0x76) : mword 64) (JAL (mword_of_int 60 : mword 21, Regidx (mword_of_int 1))) mndb_03c000ef. Qed.

  Lemma mni_7a : kernel_text -∗ instr (mword_of_int (MN + 0x7a) : mword 64) false (JAL (mword_of_int 2338 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x7a)%Z (mword_of_int 0x123000ef : mword 32)
    (mword_of_int (MN + 0x7a) : mword 64) (JAL (mword_of_int 2338 : mword 21, Regidx (mword_of_int 1))) mndb_123000ef. Qed.

  (* ---- trapinit(); trapinithart(); plicinit(); plicinithart() ---- *)

  Lemma mni_7e : kernel_text -∗ instr (mword_of_int (MN + 0x7e) : mword 64) false (JAL (mword_of_int 5382 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x7e)%Z (mword_of_int 0x506010ef : mword 32)
    (mword_of_int (MN + 0x7e) : mword 64) (JAL (mword_of_int 5382 : mword 21, Regidx (mword_of_int 1))) mndb_506010ef. Qed.

  Lemma mni_82 : kernel_text -∗ instr (mword_of_int (MN + 0x82) : mword 64) false (JAL (mword_of_int 5414 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x82)%Z (mword_of_int 0x526010ef : mword 32)
    (mword_of_int (MN + 0x82) : mword 64) (JAL (mword_of_int 5414 : mword 21, Regidx (mword_of_int 1))) mndb_526010ef. Qed.

  Lemma mni_86 : kernel_text -∗ instr (mword_of_int (MN + 0x86) : mword 64) false (JAL (mword_of_int 17786 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x86)%Z (mword_of_int 0x57a040ef : mword 32)
    (mword_of_int (MN + 0x86) : mword 64) (JAL (mword_of_int 17786 : mword 21, Regidx (mword_of_int 1))) mndb_57a040ef. Qed.

  Lemma mni_8a : kernel_text -∗ instr (mword_of_int (MN + 0x8a) : mword 64) false (JAL (mword_of_int 17808 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x8a)%Z (mword_of_int 0x590040ef : mword 32)
    (mword_of_int (MN + 0x8a) : mword 64) (JAL (mword_of_int 17808 : mword 21, Regidx (mword_of_int 1))) mndb_590040ef. Qed.

  (* ---- binit(); iinit(); fileinit(); virtio_disk_init(); userinit() ---- *)

  Lemma mni_8e : kernel_text -∗ instr (mword_of_int (MN + 0x8e) : mword 64) false (JAL (mword_of_int 7076 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x8e)%Z (mword_of_int 0x3a5010ef : mword 32)
    (mword_of_int (MN + 0x8e) : mword 64) (JAL (mword_of_int 7076 : mword 21, Regidx (mword_of_int 1))) mndb_3a5010ef. Qed.

  Lemma mni_92 : kernel_text -∗ instr (mword_of_int (MN + 0x92) : mword 64) false (JAL (mword_of_int 8438 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x92)%Z (mword_of_int 0x0f6020ef : mword 32)
    (mword_of_int (MN + 0x92) : mword 64) (JAL (mword_of_int 8438 : mword 21, Regidx (mword_of_int 1))) mndb_0f6020ef. Qed.

  Lemma mni_96 : kernel_text -∗ instr (mword_of_int (MN + 0x96) : mword 64) false (JAL (mword_of_int 12416 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x96)%Z (mword_of_int 0x080030ef : mword 32)
    (mword_of_int (MN + 0x96) : mword 64) (JAL (mword_of_int 12416 : mword 21, Regidx (mword_of_int 1))) mndb_080030ef. Qed.

  Lemma mni_9a : kernel_text -∗ instr (mword_of_int (MN + 0x9a) : mword 64) false (JAL (mword_of_int 18032 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x9a)%Z (mword_of_int 0x670040ef : mword 32)
    (mword_of_int (MN + 0x9a) : mword 64) (JAL (mword_of_int 18032 : mword 21, Regidx (mword_of_int 1))) mndb_670040ef. Qed.

  Lemma mni_9e : kernel_text -∗ instr (mword_of_int (MN + 0x9e) : mword 64) false (JAL (mword_of_int 3250 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (MN + 0x9e)%Z (mword_of_int 0x4b3000ef : mword 32)
    (mword_of_int (MN + 0x9e) : mword 64) (JAL (mword_of_int 3250 : mword 21, Regidx (mword_of_int 1))) mndb_4b3000ef. Qed.

  (* ---- the release fence, then started = 1, then back to the join ---- *)

  Lemma mni_a2 : kernel_text -∗ instr (mword_of_int (MN + 0xa2) : mword 64) false (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))).
  Proof. mk_base (MN + 0xa2)%Z (mword_of_int 0x0330000f : mword 32)
    (mword_of_int (MN + 0xa2) : mword 64) (FENCE (mword_of_int 0 : mword 4, mword_of_int 3 : mword 4, mword_of_int 3 : mword 4, Regidx (mword_of_int 0), Regidx (mword_of_int 0))) bdec_0330000f. Qed.

  Lemma mni_a6 : kernel_text -∗ instr (mword_of_int (MN + 0xa6) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)).
  Proof. mk_rvc (MN + 0xa6)%Z (mword_of_int 0x4785 : mword 16)
    (mword_of_int (MN + 0xa6) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 15), ADDI)) cdec_4785 exec_execute_C_LI. Qed.

  Lemma mni_a8 : kernel_text -∗ instr (mword_of_int (MN + 0xa8) : mword 64) false (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (MN + 0xa8)%Z (mword_of_int 0x00009717 : mword 32)
    (mword_of_int (MN + 0xa8) : mword 64) (UTYPE (mword_of_int 9 : mword 20, Regidx (mword_of_int 14), AUIPC)) mndb_00009717. Qed.

  Lemma mni_ac : kernel_text -∗ instr (mword_of_int (MN + 0xac) : mword 64) false (STORE (mword_of_int 778 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)).
  Proof. mk_base (MN + 0xac)%Z (mword_of_int 0x30f72523 : mword 32)
    (mword_of_int (MN + 0xac) : mword 64) (STORE (mword_of_int 778 : mword 12, Regidx (mword_of_int 15), Regidx (mword_of_int 14), 4)) mndb_30f72523. Qed.

  Lemma mni_b0 : kernel_text -∗ instr (mword_of_int (MN + 0xb0) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (MN + 0xb0)%Z (mword_of_int 0xb779 : mword 16)
    (mword_of_int (MN + 0xb0) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 1991 : mword 11) ('b"0")), zreg)) mndc_b779 exec_execute_C_J. Qed.

End CodeMain.

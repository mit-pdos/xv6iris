(* WpIsmappedDecode.v -- decode templates + [instr] facts for ismapped()'s
   thirteen instructions at KernelSyms.ismapped = 0x80001584.

   ismapped's 16-byte frame prologue/epilogue (c.addi sp,-16 / c.sdsp ra /
   c.sdsp s0 / c.addi4spn s0,sp,16 ... c.ldsp ra / c.ldsp s0 / c.addi sp,16 /
   c.ret) is byte-identical to kvmmap's, so those decodes reuse the shared
   [cdec_*] templates from KernelRvcDecode.v.  Its own four compressed words
   (c.li a2,0 / c.beqz a0 / c.ld a0,0(a0) / c.andi a0,1) and the jal to walk
   are decoded here.

   0xc119 (c.beqz a0,+0x06) is shared with pipealloc, so it is decoded in
   KernelRvcDecode.v as [cdec_c119] like every other multi-function word. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Values.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation IM := KernelSyms.ismapped.

(* ===================================================================== *)
(* Fresh compressed decode templates.                                     *)
(* ===================================================================== *)

(* 0x4601  c.li a2,0 -- [cdec_4601] (KernelRvcDecode.v) *)

(* 0xc119  c.beqz a0,+0x06 -- [cdec_c119] (KernelRvcDecode.v) *)

(* 0x6108  c.ld a0,0(a0) *)
Lemma imdc_6108 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6108 : mword 16)) s
  = Some (C_LD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* 0x8905  c.andi a0,a0,1 *)
Lemma imdc_8905 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8905 : mword 16)) s
  = Some (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 2)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* The base (32-bit) jal to walk.                                         *)
(* ===================================================================== *)

(* +0x0a  0x9cfff0ef  jal ra,walk (target 0x80000f5c) *)
Lemma imdb_jal_walk s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x9cfff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095566 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ===================================================================== *)
(* The leaf-friendly C_* -> base expansions for ismapped's operands.      *)
(* ===================================================================== *)

Lemma imexec_ld0_a0a0 s :
  exec (execute (C_LD (mword_of_int 0, Cregidx (mword_of_int 2), Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (LOAD (mword_of_int 0, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 8)), s).
Proof. apply exec_execute_C_LD_leaf; first [ apply bv_eq; vm_compute; reflexivity | vm_compute; reflexivity ]. Qed.

Lemma imexec_andi1_a0 s :
  exec (execute (C_ANDI (mword_of_int 1, Cregidx (mword_of_int 2)))) s
  = Some (ExecuteAs (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI)), s).
Proof. apply exec_execute_C_ANDI_leaf; vm_compute; reflexivity. Qed.

(* ===================================================================== *)
(* The [instr] facts, one per instruction.                                *)
(* ===================================================================== *)

Section WpIsmappedDecode.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  Local Notation IMP off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (IM + off) : mword 64) rvc ast).

  (* ---- prologue: 16-byte frame saving ra/s0 (shared cdec_* decodes) ---- *)
  Lemma imi_00 : IMP 0x00 true (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IM + 0x00)%Z (mword_of_int 0x1141 : mword 16) (mword_of_int (IM + 0x00) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 48 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_1141 exec_execute_C_ADDI. Qed.

  Lemma imi_02 : IMP 0x02 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (IM + 0x02)%Z (mword_of_int 0xe406 : mword 16) (mword_of_int (IM + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e406 exec_execute_C_SDSP. Qed.

  Lemma imi_04 : IMP 0x04 true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (IM + 0x04)%Z (mword_of_int 0xe022 : mword 16) (mword_of_int (IM + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e022 exec_execute_C_SDSP. Qed.

  Lemma imi_06 : IMP 0x06 true (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (IM + 0x06)%Z (mword_of_int 0x0800 : mword 16) (mword_of_int (IM + 0x06) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 4 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0800 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x08: c.li a2,0 (walk's alloc = 0) ---- *)
  Lemma imi_08 : IMP 0x08 true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)).
  Proof. mk_rvc (IM + 0x08)%Z (mword_of_int 0x4601 : mword 16) (mword_of_int (IM + 0x08) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 12), ADDI)) cdec_4601 exec_execute_C_LI. Qed.

  (* ---- +0x0a: jal walk ---- *)
  Lemma imi_0a : IMP 0x0a false (JAL (mword_of_int 2095566 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (IM + 0x0a)%Z (mword_of_int 0x9cfff0ef : mword 32) (mword_of_int (IM + 0x0a) : mword 64) (JAL (mword_of_int 2095566 : mword 21, Regidx (mword_of_int 1))) imdb_jal_walk. Qed.

  (* ---- +0x0e: c.beqz a0,+0x14 (pte == 0 -> return 0) ---- *)
  Lemma imi_0e : IMP 0x0e true (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)).
  Proof. mk_rvc (IM + 0x0e)%Z (mword_of_int 0xc119 : mword 16) (mword_of_int (IM + 0x0e) : mword 64) (BTYPE (sign_extend' 13 (concat_vec (mword_of_int 3 : mword 8) ('b"0")), zreg, creg2reg_idx (Cregidx (mword_of_int 2)), BEQ)) cdec_c119 exec_execute_C_BEQZ. Qed.

  (* ---- +0x10: c.ld a0,0(a0) (read the L0 slot word) ---- *)
  Lemma imi_10 : IMP 0x10 true (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 8)).
  Proof. mk_rvc (IM + 0x10)%Z (mword_of_int 0x6108 : mword 16) (mword_of_int (IM + 0x10) : mword 64) (LOAD (mword_of_int 0 : mword 12, Regidx (mword_of_int 10), Regidx (mword_of_int 10), false, 8)) imdc_6108 imexec_ld0_a0a0. Qed.

  (* ---- +0x12: c.andi a0,a0,1 (the V bit) ---- *)
  Lemma imi_12 : IMP 0x12 true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI)).
  Proof. mk_rvc (IM + 0x12)%Z (mword_of_int 0x8905 : mword 16) (mword_of_int (IM + 0x12) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), Regidx (mword_of_int 10), Regidx (mword_of_int 10), ANDI)) imdc_8905 imexec_andi1_a0. Qed.

  (* ---- +0x14..+0x1a: epilogue (shared cdec_* decodes) ---- *)
  Lemma imi_14 : IMP 0x14 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (IM + 0x14)%Z (mword_of_int 0x60a2 : mword 16) (mword_of_int (IM + 0x14) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), sp, Regidx (mword_of_int 1), false, 8)) cdec_60a2 exec_execute_C_LDSP. Qed.

  Lemma imi_16 : IMP 0x16 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (IM + 0x16)%Z (mword_of_int 0x6402 : mword 16) (mword_of_int (IM + 0x16) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), sp, Regidx (mword_of_int 8), false, 8)) cdec_6402 exec_execute_C_LDSP. Qed.

  Lemma imi_18 : IMP 0x18 true (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)).
  Proof. mk_rvc (IM + 0x18)%Z (mword_of_int 0x0141 : mword 16) (mword_of_int (IM + 0x18) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 16 : mword 6), Regidx csp_rs1, Regidx csp_rs1, ADDI)) cdec_0141 exec_execute_C_ADDI. Qed.

  Lemma imi_1a : IMP 0x1a true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (IM + 0x1a)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (IM + 0x1a) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End WpIsmappedDecode.

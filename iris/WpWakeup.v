(* WpWakeup.v -- the per-process spinlock invariant of xv6's [struct proc],
   the global [proc[NPROC]] lock invariant, and (later) a whole-function WP for
   wakeup().

   Layout of [struct proc] (kernel/proc.h), corroborated by the compiled
   wakeup disassembly (KernelInstrs.v):

       offset 0    struct spinlock lock;   (locked word at +0, cpu ptr at +16)
       offset 24   enum procstate state;   (4-byte int; SLEEPING=2, RUNNABLE=3)
       offset 32   void *chan;             (8-byte)
       ...
       offset 96   struct context context; (14 * 8 = 112 bytes: ra,sp,s0..s11)
       ...
       sizeof(struct proc) = 360,  NPROC = 64,  proc[] @ 0x80012778.

   [proc_lock_res γ p] is the resource protected by [p->lock]: it fully owns
   [p->state] and [p->chan], and -- WHENEVER the state is RUNNABLE or SLEEPING
   -- a [valid_context P (&p->context)] whose resumer-predicate P carries the
   lock's own [locked γ] token.  This encodes the sleep/wakeup handoff: to
   swtch INTO a runnable/sleeping proc you must hand it the lock (P delivers
   [locked γ]); when it wakes it is running holding its own lock.

   [procs_inv γs] is the global fact that every one of the NPROC procs has a
   spinlock guarding its own [proc_lock_res]. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.algebra Require Import excl ofe.
From iris.base_logic.lib Require Import invariants own ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import RegFile.
Require Import InstrBytes RiscvFetchExec KernelText.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import VcGen.
Require Import RiscvExec RiscvExtras RiscvTryStep WpDecode WpRvcBridge.
From Kernel Require Import KernelSyms KernelInstrs.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase.
Require Export ProcGeom.
Require Import KernelRvcDecode.
Local Open Scope Z_scope.
Import Defs.

(* ======================================================================= *)
(* Instruction DECODE facts for wakeup's instructions.  Base instrs decode  *)
(* via [decode_any]; compressed instrs decode to their [C_*] form and then   *)
(* bridge to the executable [ExecuteAs (...)] form.  (Same apparatus as      *)
(* WpSwtchVc / WpTimerinit.)  Register indices: ra=1 sp=2 s0=8 s1=9 a0=10    *)
(* a5=15 s2=18 s3=19 s4=20 s5=21.  wakeup base = 0x80001f44.                  *)
(* ======================================================================= *)

(* ---- base instructions ---- *)
(* 0x80001f58 auipc s1,0x11 *)
Lemma wkd_f58 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00011497 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f5c addi s1,s1,-2016 *)
Lemma wkd_f5c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x81248493 : mword 32)) s
  = Some (ITYPE (mword_of_int 2066 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f64 auipc s2,0x16 *)
Lemma wkd_f64 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00016917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f68 addi s2,s2,532 *)
Lemma wkd_f68 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x20690913 : mword 32)) s
  = Some (ITYPE (mword_of_int 518 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f74 addi s1,s1,360 *)
Lemma wkd_f74 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x16848493 : mword 32)) s
  = Some (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f78 beq s1,s2,+36 *)
Lemma wkd_f78 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03248263 : mword 32)) s
  = Some (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f80 beq a0,s1,-12 *)
Lemma wkd_f80 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfe950ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 10), BEQ), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f8c bne a5,s3,-30 *)
Lemma wkd_f8c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff3791e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f92 bne a5,s4,-36 *)
Lemma wkd_f92 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xfd479ee3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f96 sw s5,24(s1) *)
Lemma wkd_f96 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0154ac23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f70 jal release (-4846) *)
Lemma wkd_f70 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xd13fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092306 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f7c jal myproc (-1670) *)
Lemma wkd_f7c s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x97bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095482 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.
(* 0x80001f86 jal acquire (-5004) *)
Lemma wkd_f86 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xc75fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* ---- compressed instructions (misa.C + rvc_oneshot; ext_decode_compressed) ---- *)
(* 0x80001f60 c.li s3,2 ; 0x80001f62 c.li s5,3 *)
Lemma wkd_f60 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4989 : mword 16)) s
  = Some (C_LI (mword_of_int 2, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f62 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4a8d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f6c c.j +16 ; 0x80001f9a c.j -44 *)
Lemma wkd_f6c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa801 : mword 16)) s
  = Some (C_J (mword_of_int 8 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f9a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbfd1 : mword 16)) s
  = Some (C_J (mword_of_int 2026 : mword 11), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f8a c.lw a5,24(s1) *)
Lemma wkd_f8a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4c9c : mword 16)) s
  = Some (C_LW (mword_of_int 6, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f90 c.ld a5,32(s1) *)
Lemma wkd_f90 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x709c : mword 16)) s
  = Some (C_LD (mword_of_int 4, Cregidx (mword_of_int 1), Cregidx (mword_of_int 7)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* struct proc / struct cpu geometry (NPROC, proc_addr, p_state/p_chan/
   p_context, state codes, needs_ctx, proc_addr_succ, ...) now lives in
   ProcGeom.v, re-exported above. *)

(* ====================================================================== *)
(* The prologue as a VCgen block: [c.addi16sp sp,-64] + 7 register saves +  *)
(* [c.addi4spn s0,sp,64] (wakeup 0x00..0x10).  Symbolic slot contents use   *)
(* the fresh indices 33..39 (unused by any register).                        *)
(* ====================================================================== *)


(* The epilogue straight run at 0x58..0x66: the seven [c.ldsp] restores of
   ra/s0/s1..s5, then [c.addi16sp sp,+64] to pop the frame.  Loads leave the
   frame memory unchanged, so the post-heap equals the input frame. *)


Section WkLeaves.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* c.li rd, imm  ==  addi rd, x0, sext(imm) : writes sext(imm) into rd.
     Mirrors wp_caddi_gpr_s_config_pt but with rs1 = x0 (so the value is the
     immediate, not rd+imm).  Discharged through wp_gpr_write_s_config_pt. *)

  (* ---- instruction fact builders (verbatim from WpSwtchVc) ---- *)
  Local Notation WKI off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.wakeup + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))) (only parsing).
  Local Notation cld_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 5) ('b"000"))) (only parsing).

  (* ---- prologue ---- *)
  Lemma wki_00 : WKI 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x00)%Z (mword_of_int 0x7139 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) cdec_7139 exec_execute_C_ADDI16SP. Qed.
  Lemma wki_02 : WKI 0x02 true (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x02)%Z (mword_of_int 0xfc06 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x02) : mword 64) (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)) cdec_fc06 exec_execute_C_SDSP. Qed.
  Lemma wki_04 : WKI 0x04 true (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x04)%Z (mword_of_int 0xf822 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x04) : mword 64) (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)) cdec_f822 exec_execute_C_SDSP. Qed.
  Lemma wki_06 : WKI 0x06 true (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x06)%Z (mword_of_int 0xf426 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x06) : mword 64) (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)) cdec_f426 exec_execute_C_SDSP. Qed.
  Lemma wki_08 : WKI 0x08 true (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x08)%Z (mword_of_int 0xf04a : mword 16) (mword_of_int (KernelSyms.wakeup + 0x08) : mword 64) (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)) cdec_f04a exec_execute_C_SDSP. Qed.
  Lemma wki_0a : WKI 0x0a true (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x0a)%Z (mword_of_int 0xec4e : mword 16) (mword_of_int (KernelSyms.wakeup + 0x0a) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)) cdec_ec4e exec_execute_C_SDSP. Qed.
  Lemma wki_0c : WKI 0x0c true (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x0c)%Z (mword_of_int 0xe852 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x0c) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)) cdec_e852 exec_execute_C_SDSP. Qed.
  Lemma wki_0e : WKI 0x0e true (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x0e)%Z (mword_of_int 0xe456 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x0e) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)) cdec_e456 exec_execute_C_SDSP. Qed.
  Lemma wki_10 : WKI 0x10 true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x10)%Z (mword_of_int 0x0080 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0080 exec_execute_C_ADDI4SPN. Qed.
  Lemma wki_12 : WKI 0x12 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x12)%Z (mword_of_int 0x8a2a : mword 16) (mword_of_int (KernelSyms.wakeup + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) cdec_8a2a exec_execute_C_MV. Qed.
  Lemma wki_14 : WKI 0x14 false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KernelSyms.wakeup + 0x14)%Z (mword_of_int 0x00011497 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x14) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)) wkd_f58. Qed.
  Lemma wki_18 : WKI 0x18 false (ITYPE (mword_of_int 2066 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.wakeup + 0x18)%Z (mword_of_int 0x81248493 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x18) : mword 64) (ITYPE (mword_of_int 2066 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) wkd_f5c. Qed.
  Lemma wki_1c : WKI 0x1c true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x1c)%Z (mword_of_int 0x4989 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) wkd_f60 exec_execute_C_LI. Qed.
  Lemma wki_1e : WKI 0x1e true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x1e)%Z (mword_of_int 0x4a8d : mword 16) (mword_of_int (KernelSyms.wakeup + 0x1e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)) wkd_f62 exec_execute_C_LI. Qed.
  Lemma wki_20 : WKI 0x20 false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KernelSyms.wakeup + 0x20)%Z (mword_of_int 0x00016917 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x20) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)) wkd_f64. Qed.
  Lemma wki_24 : WKI 0x24 false (ITYPE (mword_of_int 518 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KernelSyms.wakeup + 0x24)%Z (mword_of_int 0x20690913 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x24) : mword 64) (ITYPE (mword_of_int 518 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) wkd_f68. Qed.
  Lemma wki_28 : WKI 0x28 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x28)%Z (mword_of_int 0xa801 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x28) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)) wkd_f6c exec_execute_C_J. Qed.
  (* ---- loop / release path ---- *)
  Lemma wki_2a : WKI 0x2a true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x2a)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma wki_2c : WKI 0x2c false (JAL (mword_of_int 2092306 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.wakeup + 0x2c)%Z (mword_of_int 0xd13fe0ef : mword 32) (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) (JAL (mword_of_int 2092306 : mword 21, Regidx (mword_of_int 1))) wkd_f70. Qed.
  Lemma wki_30 : WKI 0x30 false (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.wakeup + 0x30)%Z (mword_of_int 0x16848493 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x30) : mword 64) (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) wkd_f74. Qed.
  Lemma wki_34 : WKI 0x34 false (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (KernelSyms.wakeup + 0x34)%Z (mword_of_int 0x03248263 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64) (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)) wkd_f78. Qed.
  Lemma wki_38 : WKI 0x38 false (JAL (mword_of_int 2095482 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.wakeup + 0x38)%Z (mword_of_int 0x97bff0ef : mword 32) (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) (JAL (mword_of_int 2095482 : mword 21, Regidx (mword_of_int 1))) wkd_f7c. Qed.
  Lemma wki_3c : WKI 0x3c false (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 10), BEQ)).
  Proof. mk_base (KernelSyms.wakeup + 0x3c)%Z (mword_of_int 0xfe950ae3 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64) (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 10), BEQ)) wkd_f80. Qed.
  Lemma wki_40 : WKI 0x40 true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x40)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.
  Lemma wki_42 : WKI 0x42 false (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.wakeup + 0x42)%Z (mword_of_int 0xc75fe0ef : mword 32) (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1))) wkd_f86. Qed.
  Lemma wki_46 : WKI 0x46 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x46)%Z (mword_of_int 0x4c9c : mword 16) (mword_of_int (KernelSyms.wakeup + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) wkd_f8a exec_execute_C_LW. Qed.
  Lemma wki_48 : WKI 0x48 false (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.wakeup + 0x48)%Z (mword_of_int 0xff3791e3 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)) wkd_f8c. Qed.
  Lemma wki_4c : WKI 0x4c true (LOAD (cld_imm 4, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x4c)%Z (mword_of_int 0x709c : mword 16) (mword_of_int (KernelSyms.wakeup + 0x4c) : mword 64) (LOAD (cld_imm 4, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) wkd_f90 exec_execute_C_LD. Qed.
  Lemma wki_4e : WKI 0x4e false (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.wakeup + 0x4e)%Z (mword_of_int 0xfd479ee3 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE)) wkd_f92. Qed.
  Lemma wki_52 : WKI 0x52 false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (KernelSyms.wakeup + 0x52)%Z (mword_of_int 0x0154ac23 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4)) wkd_f96. Qed.
  Lemma wki_56 : WKI 0x56 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x56)%Z (mword_of_int 0xbfd1 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x56) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)) wkd_f9a exec_execute_C_J. Qed.
  (* ---- epilogue ---- *)
  Lemma wki_58 : WKI 0x58 true (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x58)%Z (mword_of_int 0x70e2 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x58) : mword 64) (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)) cdec_70e2 exec_execute_C_LDSP. Qed.
  Lemma wki_5a : WKI 0x5a true (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x5a)%Z (mword_of_int 0x7442 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x5a) : mword 64) (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)) cdec_7442 exec_execute_C_LDSP. Qed.
  Lemma wki_5c : WKI 0x5c true (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x5c)%Z (mword_of_int 0x74a2 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x5c) : mword 64) (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)) cdec_74a2 exec_execute_C_LDSP. Qed.
  Lemma wki_5e : WKI 0x5e true (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x5e)%Z (mword_of_int 0x7902 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x5e) : mword 64) (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)) cdec_7902 exec_execute_C_LDSP. Qed.
  Lemma wki_60 : WKI 0x60 true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x60)%Z (mword_of_int 0x69e2 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x60) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)) cdec_69e2 exec_execute_C_LDSP. Qed.
  Lemma wki_62 : WKI 0x62 true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x62)%Z (mword_of_int 0x6a42 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x62) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)) cdec_6a42 exec_execute_C_LDSP. Qed.
  Lemma wki_64 : WKI 0x64 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x64)%Z (mword_of_int 0x6aa2 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x64) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)) cdec_6aa2 exec_execute_C_LDSP. Qed.
  Lemma wki_66 : WKI 0x66 true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x66)%Z (mword_of_int 0x6121 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x66) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) cdec_6121 exec_execute_C_ADDI16SP. Qed.
  Lemma wki_68 : WKI 0x68 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc (KernelSyms.wakeup + 0x68)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x68) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

  (* the prologue block's [instr] facts, assembled from the [wki_*] templates. *)

  (* the epilogue block's [instr] facts, assembled from the [wki_*] templates. *)

End WkLeaves.

(* ======================================================================= *)
(* Leaf lemmas specific to wakeup's instruction mix that were not already   *)
(* available: the compressed [c.li rd, imm] (ADDI from x0).                  *)

Section WkScfgLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.









End WkScfgLeaves.

(* The per-proc lock invariant ([proc_lock_res] / [procs_inv]), the parked
   context obligation ([proc_ctx]) and their intro/elim/wakeup lemmas moved
   to SchedCtx.v (built on the sconf-γ swtch protocol), superseding the old
   smode-config / [contains_lock]-based versions that used to live here.
   WpWakeup keeps only the decode/leaf/loop-arithmetic content below. *)
Section ProcInv.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* ===================================================================== *)
  (* Resource layout for the wakeup() WP.                                   *)
  (*                                                                        *)
  (* [spF] is wakeup's frame pointer -- the sp value AFTER the [c.addi16sp  *)
  (* sp,-64] prologue.  acquire/release are called with sp = spF and place  *)
  (* their spill/push_off/mycpu scratch BELOW spF at the exact offsets       *)
  (* recomputed here (so these cells UNIFY with the acquire/release specs).  *)
  (* ===================================================================== *)


  (* the current cpu's per-cpu push_off bookkeeping words, at cpu+120/+124.
     [noff] is restored to its entry value by each acquire/release pair;
     [intena] stays 0 throughout (our S-mode config has SIE=0). *)
  Definition wk_noff_addr (a0f : mword 64) : mword 64 :=
    add_vec a0f (sign_extend' 64 (mword_of_int 120 : mword 12)).
  Definition wk_intena_addr (a0f : mword 64) : mword 64 :=
    add_vec a0f (sign_extend' 64 (mword_of_int 124 : mword 12)).

  (* the lock->cpu word of every proc, all 0 at each loop-test (acquire sets it
     to mycpu, release clears it back to 0). *)
  Definition wk_cpu_addr (pa : mword 64) : mword 64 :=
    add_vec pa (sign_extend' 64 (mword_of_int 16 : mword 12)).
  Definition wk_lockcells (γs : list gname) : iProp Σ :=
    ([∗ list] i ↦ _ ∈ γs, wk_cpu_addr (proc_addr i) ↦₈ (zero_reg : mword 64))%I.

  (* wakeup's own 7-entry register-save frame, at spF+8..spF+56 (written by the
     [c.sdsp] prologue, read back by the epilogue).  Cell addresses are given in
     the [c.sdsp] leaf's own form [add_vec spF (sign_extend' 64 (csdsp_imm u))]. *)
  Definition wk_fcell (spF : mword 64) (u : Z) : mword 64 :=
    add_vec spF (zero_extend' 64 (concat_vec (mword_of_int u : mword 6) ('b"000"))).
  Definition wk_frame (spF : mword 64) (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64) : iProp Σ :=
    (wk_fcell spF 7 ↦₈ vra ∗ wk_fcell spF 6 ↦₈ vs0 ∗ wk_fcell spF 5 ↦₈ vs1 ∗
     wk_fcell spF 4 ↦₈ vs2 ∗ wk_fcell spF 3 ↦₈ vs3 ∗ wk_fcell spF 2 ↦₈ vs4 ∗
     wk_fcell spF 1 ↦₈ vs5)%I.

  (* the mutable stack/lock/percpu resources that the loop threads; [noffv] is
     the (fixed) entry noff, restored by each acquire/release pair.  The scratch
     region is a single [stack_own spF n] for any depth [n >= 10] that covers the
     acquire/release frame -- the loop never needs a precise [n]. *)

  (* register-map shape at the loop test [pc = wakeup+0x38] with counter [i]:
     the loop/callee-saved registers hold their fixed values (a0/a5 are scratch,
     hence existential in the map). *)

  (* ===================================================================== *)
  (* Prologue: wakeup+0x00 .. the [c.j] to the loop test at wakeup+0x38.     *)
  (* Saves ra/s0/s1..s5, sets up s1=&proc[0], s2=&proc[64], s3=SLEEPING,     *)
  (* s4=chan, s5=RUNNABLE, then jumps to the loop test.                      *)
  (* ===================================================================== *)
  (* peel nested [<[k:=v]>_ !!! j] map lookups down to the base map. *)
  Local Ltac wk_peel :=
    repeat first
      [ rewrite upd_eq
      | (rewrite upd_ne; [ idtac | vm_compute; discriminate ]) ].


  (* ===================================================================== *)
  (* Epilogue: wakeup+0x58 (the [DONE] label) .. the [c.ret].               *)
  (* Restores ra/s0/s1..s5 from the frame, pops the 64-byte frame, and      *)
  (* returns to the (bit-0-cleared) saved return address.                   *)
  (* ===================================================================== *)

  (* register-map shape at the loop header [pc = wakeup+0x38] with counter [k].
     Same as [wk_regs] but WITHOUT the [ra] constraint: [ra] is dead at the
     header (immediately clobbered by the [jal myproc]). *)
  Definition wk_loop_regs (M : regfile) (spF rtp chan : mword 64)
      (vs6 vs7 vs8 vs9 vs10 vs11 : mword 64) (k : nat) : Prop :=
    M !!! Regidx (mword_of_int 9)  = proc_addr k /\
    M !!! Regidx (mword_of_int 2)  = spF /\
    M !!! Regidx (mword_of_int 4)  = rtp /\
    M !!! Regidx (mword_of_int 18) = proc_addr NPROC /\
    M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64) /\
    M !!! Regidx (mword_of_int 20) = chan /\
    M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
    M !!! Regidx (mword_of_int 22) = vs6 /\
    M !!! Regidx (mword_of_int 23) = vs7 /\
    M !!! Regidx (mword_of_int 24) = vs8 /\
    M !!! Regidx (mword_of_int 25) = vs9 /\
    M !!! Regidx (mword_of_int 26) = vs10 /\
    M !!! Regidx (mword_of_int 27) = vs11 /\
    (forall r : regidx, r ∈ dom (rf_to_gmap M)).

  (* eq_vec is reflexive: used at the termination beq to derive that the last
     iteration index k+1 must be < NPROC (else proc_addr equal -> beq taken). *)
  Lemma wk_eq_vec_refl {n} (x : mword n) : eq_vec x x = true.
  Proof. apply eq_vec_true_iff. reflexivity. Qed.

  (* adding the (zero) offset [sext 0] is a noop: release's lock-word address is
     [add_vec lk0 (sext 0)], which must equal the lock's base [proc_addr k]. *)
  Lemma wk_add_vec_0 (x : mword 64) :
    add_vec x (sign_extend' 64 (mword_of_int 0 : mword 12)) = x.
  Proof. apply bv_add_0_r. vm_compute. reflexivity. Qed.

  (* a state cell holding a value whose 64-bit sign-extension is 2 is SLEEPING;
     used in the wake path where the c.lw-loaded [sext st] compared equal to
     s3 = 2. *)
  Lemma wk_sext_sleeping (st : mword 32) :
    sign_extend' 64 st = (mword_of_int 2 : mword 64) -> st = SLEEPING.
  Proof.
    intro H.
    assert (Ht : trunc32 (sign_extend' 64 st) = trunc32 (mword_of_int 2 : mword 64))
      by (rewrite H; reflexivity).
    rewrite trunc32_sext in Ht. rewrite Ht. apply bv_eq; vm_compute; reflexivity.
  Qed.

  (* compressed-register decode: c.lw/c.ld/c.sw name x9 (s1) and x15 (a5). *)
  Lemma wk_cr1 : creg2reg_idx (Cregidx (mword_of_int 1)) = Regidx (mword_of_int 9 : mword 5).
  Proof. vm_compute. reflexivity. Qed.
  Lemma wk_cr7 : creg2reg_idx (Cregidx (mword_of_int 7)) = Regidx (mword_of_int 15 : mword 5).
  Proof. vm_compute. reflexivity. Qed.
  (* [csp_rs1] (the c.*sp base encoding) is register x2 (sp). *)

  (* the noff word as rewritten by acquire's push_off (noff+1, truncated to 32)
     and, one round later, by release's pop_off (noff-1).  The loop threads the
     entry value [noffv] through an acquire/release pair each iteration; the two
     hypotheses [wk_noff_acq >s 0] and [round-trip = noffv] let it close. *)
  Definition wk_noff_acq (nv : mword 32) : mword 32 :=
    autocast (T := mword) (subrange_vec_dec
      (sign_extend' 64 (subrange_vec_dec
         (add_vec (sign_extend' 64 nv)
            (sign_extend' 64 (sign_extend' 12 (mword_of_int 1 : mword 6)))) 31 0))
      (Z.sub (Z.mul 4 8) 1) 0).
  Definition wk_noff_rel (nv : mword 32) : mword 32 :=
    autocast (T := mword) (subrange_vec_dec
      (sign_extend' 64 (subrange_vec_dec
         (add_vec (sign_extend' 64 nv)
            (sign_extend' 64 (sign_extend' 12 (mword_of_int 63 : mword 6)))) 31 0))
      (Z.sub (Z.mul 4 8) 1) 0).

  (* ===================================================================== *)
  (* The loop: wakeup+0x38 (loop header) .. iterating over proc[k], k<NPROC. *)
  (* Each iteration calls myproc (skip-self), acquire, checks state/chan,     *)
  (* wakes (state:=RUNNABLE) if SLEEPING on [chan], releases, p++, and either *)
  (* falls to the next iteration or exits to the epilogue at wakeup+0x58.     *)
  (* Proved by Löb induction on the counter [k].                              *)
  (* ===================================================================== *)

  (* the prologue's exit register shape [wk_regs .. k] refines the loop's
     entry shape [wk_loop_regs .. k] (NPROC = 64, so proc_addr NPROC = proc_addr 64;
     the extra [ra] constraint is simply dropped). *)

  (* the epilogue restores sp by [+60][+4], which cancels the prologue's
     [-64] frame allocation, so the final sp equals the caller's sp. *)
  Lemma wakeup_sp_cancel (X : mword 64) :
    add_vec (add_vec X (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))
            (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))) = X.
  Proof.
    assert (add_vec_unsigned : forall x y : mword 64,
              bv_unsigned (add_vec x y) = bv_wrap 64 (bv_unsigned x + bv_unsigned y)).
    { intros x y. unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
        SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
      rewrite bv_add_unsigned. reflexivity. }
    apply bv_eq. rewrite !add_vec_unsigned. rewrite bv_wrap_add_idemp_l.
    assert (HA : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6)) : mword 64) = 18446744073709551552) by (vm_compute; reflexivity).
    assert (HB : bv_unsigned (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)) : mword 64) = 64) by (vm_compute; reflexivity).
    rewrite HA HB. rewrite <- Z.add_assoc.
    replace (18446744073709551552 + 64) with (bv_modulus 64) by (vm_compute; reflexivity).
    rewrite bv_wrap_add_modulus_1. apply bv_wrap_bv_unsigned.
  Qed.

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan): prologue -> loop (k=0, exiting to  *)
  (* the epilogue) -> return.  The caller provides the callee-save frame     *)
  (* cells, the per-cpu push_off scratch/lock words ([wk_res]), and the      *)
  (* global proc-array lock invariant ([procs_inv]).  The three arithmetic   *)
  (* side conditions ([mycpu] non-null, push_off/pop_off noff round-trip)    *)
  (* are the caller's obligations on the current cpu's bookkeeping.          *)
  (* ===================================================================== *)

End ProcInv.

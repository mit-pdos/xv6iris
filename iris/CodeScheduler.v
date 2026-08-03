(* CodeScheduler.v -- decode templates + [instr] facts for scheduler()'s
   instructions at KernelSyms.scheduler = 0x80001d7a (0x1d7a .. 0x1e1d; the
   next symbol, [sched], starts at 0x80001e1e).

   scheduler() is the per-CPU dispatch loop.  Its 80-byte frame saves
   ra/s0/s1/s2/s3/s4/s5/s6/s7/s8 and it never returns, so there is no
   epilogue: the whole function is prologue, a scan of proc[] guarded by
   acquire/release, a [swtch] into the chosen process, and the loop head's
   inlined intr_on/intr_off ([csrsi]/[csrci sstatus,2]) around a [wfi].

   NAMING.  Decode templates are keyed by the instruction WORD
   ([schdec_<word>]) -- the convention KernelRvcDecode.v asks new decodes to
   use, and the one that stays correct when the same word appears at several
   offsets (0x8526 at +0x4a/+0x58, 0x00010717 at +0x20/+0x2e).  The [instr]
   facts are keyed by BYTE OFFSET from [SC] ([schi_<off>]), so a listing
   address maps straight to a lemma name.

   SHARED WORDS.  The 80-byte frame's c.addi16sp/ten c.sdsp/c.addi4spn, the
   a5-materialization triple (c.mv a5,tp / sext.w / c.slli a5,7), c.mv a0,s1,
   c.li s7,1, c.lw a5,24(s1) (with its leaf shape [cexec_lw24_s1_a5]) and
   c.mv a0,s6 all come from KernelRvcDecode.v's [cdec_*]; [addi s1,s1,360] (the
   [sizeof(struct proc)] stride), the three [auipc] relocations and the
   [csrsi sstatus,2] come from KernelBaseDecode.v's [bdec_*].  Nothing here
   imports another function's decode or WP file.

   The two CSRImm words are stated with the csr field as [Ox"100"], which is
   exactly (delta-)equal to the [csr_sstatus] that WpSconfCsr.v's csrsi/csrci
   leaves are phrased with, so those leaves apply directly. *)
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
Require Import KernelBaseDecode.
Require Import WpRvcBridge.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import WpDecodeBridge.
From iris.base_logic.lib Require Import invariants.
Local Open Scope Z_scope.
Import Defs.

Notation SC := KernelSyms.scheduler.

(* ===================================================================== *)
(* Fresh compressed decode templates (keyed by word).                     *)
(* ===================================================================== *)

(* [cdec_e062] (+0x14, c.sdsp s8,0(sp)) -- shared, see KernelRvcDecode.v *)

(* +0x28  0x975a  c.add a4,a4,s6 *)
Lemma schdec_975a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x975a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 14), Regidx (mword_of_int 22)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x36  0x9b3a  c.add s6,s6,a4 *)
Lemma schdec_9b3a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9b3a : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 22), Regidx (mword_of_int 14)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x38  0x4c11  c.li s8,4  (RUNNABLE -> RUNNING) *)
Lemma schdec_4c11 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4c11 : mword 16)) s
  = Some (C_LI (mword_of_int 4, Regidx (mword_of_int 24)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x44  0x9a3e  c.add s4,s4,a5 *)
Lemma schdec_9a3e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x9a3e : mword 16)) s
  = Some (C_ADD (Regidx (mword_of_int 20), Regidx (mword_of_int 15)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_4b85] (+0x46, c.li s7,1 -- the "found a runnable proc" flag) --
   shared, see KernelRvcDecode.v *)

(* +0x48  0xa83d  c.j +0x3e  (into the loop head at +0x86) *)
Lemma schdec_a83d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xa83d : mword 16)) s
  = Some (C_J (mword_of_int 31), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* [cdec_4c9c] (+0x5e, c.lw a5,24(s1) -- p->state) and its leaf-form shape
   [cexec_lw24_s1_a5] -- shared, see KernelRvcDecode.v *)

(* [cdec_855a] (+0x70, c.mv a0,s6 -- &c->context, swtch's first argument) --
   shared, see KernelRvcDecode.v *)

(* +0x7a  0x8ade  c.mv s5,s7 *)
Lemma schdec_8ade s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8ade : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 21), Regidx (mword_of_int 23)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x7c  0xb7f9  c.j -0x32  (back to the release at +0x4a) *)
Lemma schdec_b7f9 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xb7f9 : mword 16)) s
  = Some (C_J (mword_of_int 2023), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x8e  0x4a81  c.li s5,0 *)
Lemma schdec_4a81 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x4a81 : mword 16)) s
  = Some (C_LI (mword_of_int 0, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0x98  0x498d  c.li s3,3  (RUNNABLE) *)
Lemma schdec_498d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x498d : mword 16)) s
  = Some (C_LI (mword_of_int 3, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* +0xa2  0xbf5d  c.j -0x4a  (back to the acquire at +0x58) *)
Lemma schdec_bf5d s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xbf5d : mword 16)) s
  = Some (C_J (mword_of_int 2011), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* ===================================================================== *)
(* Fresh base (32-bit) decode templates (keyed by word).                  *)
(* ===================================================================== *)

(* +0x1c  0x00779b13  slli s6,a5,0x7 *)
Lemma schdec_00779b13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00779b13 : mword 32)) s
  = Some (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 22), SLLI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* [bdec_00010717] (+0x20, +0x2e, auipc a4,0x10) -- shared, see
   KernelBaseDecode.v *)

(* +0x24  0x5ae70713  addi a4,a4,1454  (&pid_lock, i.e. cpus[] via +0x30) *)
Lemma schdec_5ae70713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5ae70713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1454 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x2a  0x02073823  sd zero,48(a4)  (c->proc = 0) *)
Lemma schdec_02073823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x02073823 : mword 32)) s
  = Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x32  0x5d870713  addi a4,a4,1496  (&cpus[0].context) *)
Lemma schdec_5d870713 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5d870713 : mword 32)) s
  = Some (ITYPE (mword_of_int 1496 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x3c  0x00010a17  auipc s4,0x10 *)
Lemma schdec_00010a17 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x00010a17 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 20), AUIPC), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x40  0x592a0a13  addi s4,s4,1426  (&pid_lock; s4 = &cpus[cpuid()]) *)
Lemma schdec_592a0a13 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x592a0a13 : mword 32)) s
  = Some (ITYPE (mword_of_int 1426 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x4c  0xecbfe0ef  jal ra,release (target 0x80000c90; offset -4406) *)
Lemma schdec_ecbfe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xecbfe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092746 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x54  0x03248563  beq s1,s2,+0x2a  (end of the proc[] scan) *)
Lemma schdec_03248563 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x03248563 : mword 32)) s
  = Some (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x5a  0xe35fe0ef  jal ra,acquire (target 0x80000c08; offset -4556) *)
Lemma schdec_e35fe0ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xe35fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092596 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x60  0xff3795e3  bne a5,s3,-0x16  (p->state != RUNNABLE) *)
Lemma schdec_ff3795e3 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0xff3795e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x64  0x0184ac23  sw s8,24(s1)  (p->state = RUNNING) *)
Lemma schdec_0184ac23 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x0184ac23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 9), 4), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x68  0x029a3823  sd s1,48(s4)  (c->proc = p) *)
Lemma schdec_029a3823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x029a3823 : mword 32)) s
  = Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 20), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x6c  0x06048593  addi a1,s1,96  (&p->context, swtch's second argument) *)
Lemma schdec_06048593 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x06048593 : mword 32)) s
  = Some (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x72  0x5ac000ef  jal ra,swtch (target 0x80002398; offset +1452) *)
Lemma schdec_5ac000ef s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x5ac000ef : mword 32)) s
  = Some (JAL (mword_of_int 1452 : mword 21, Regidx (mword_of_int 1)), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x76  0x020a3823  sd zero,48(s4)  (c->proc = 0) *)
Lemma schdec_020a3823 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x020a3823 : mword 32)) s
  = Some (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 20), 8), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x7e  0x000a9463  bnez s5,+8  (skip the wfi if a proc ran) *)
Lemma schdec_000a9463 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x000a9463 : mword 32)) s
  = Some (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BNE), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* +0x82  0x10500073  wfi *)
Lemma schdec_10500073 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10500073 : mword 32)) s
  = Some (WFI tt, s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* [bdec_10016073] (+0x86, csrsi sstatus,2 -- intr_on, rd = x0) -- shared, see
   KernelBaseDecode.v.  Its twin below is this file's only [decode_bridge_ms_bv]
   word: [decode_bridge_ms]'s bare [vm_compute; reflexivity] cannot close the
   concrete decode, because the decoder's 5-bit uimm arrives as a SLICE of the
   instruction word while the CSR leaves (WpSconfCsr.v) phrase it as
   [mword_of_int 2], and only [bv_eq] closes that; [Ox"100"] is the
   [csr_sstatus] those leaves are stated with. *)

(* +0x8a  0x10017073  csrci sstatus,2  (intr_off, rd = x0) *)
Lemma schdec_10017073 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x10017073 : mword 32)) s
  = Some (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRC), s).
Proof. decode_bridge_ms_bv. Qed.

(* [bdec_00011497] (+0x90, auipc s1,0x11) -- shared, see KernelBaseDecode.v *)

(* +0x94  0x96e48493  addi s1,s1,-1682  (&proc[0]; residue 2414) *)
Lemma schdec_96e48493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x96e48493 : mword 32)) s
  = Some (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

(* [bdec_00016917] (+0x9a, auipc s2,0x16) -- shared, see KernelBaseDecode.v *)

(* +0x9e  0x36490913  addi s2,s2,868  (&proc[NPROC], the scan's limit) *)
Lemma schdec_36490913 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s ->
  exec (ext_decode (mword_of_int 0x36490913 : mword 32)) s
  = Some (ITYPE (mword_of_int 868 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. first [ decode_bridge_ms | intros Hbm Hcfg; destruct Hcfg as [[Hpriv _]|[Hpriv _]]; decode_any s Hpriv ]. Qed.

Section CodeScheduler.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* ---- +0x00..+0x16: 80-byte frame, saves ra/s0/s1/s2/s3/s4/s5/s6/s7/s8 ---- *)
  Lemma schi_00 : kernel_text -∗ instr (mword_of_int (SC + 0x00) : mword 64) true (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc (SC + 0x00)%Z (mword_of_int 0x715d : mword 16)
    (mword_of_int (SC + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 59 : mword 6), sp, sp, ADDI)) cdec_715d exec_execute_C_ADDI16SP. Qed.

  Lemma schi_02 : kernel_text -∗ instr (mword_of_int (SC + 0x02) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc (SC + 0x02)%Z (mword_of_int 0xe486 : mword 16)
    (mword_of_int (SC + 0x02) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 9 : mword 6) ('b"000")), Regidx (mword_of_int 1), sp, 8)) cdec_e486 exec_execute_C_SDSP. Qed.

  Lemma schi_04 : kernel_text -∗ instr (mword_of_int (SC + 0x04) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc (SC + 0x04)%Z (mword_of_int 0xe0a2 : mword 16)
    (mword_of_int (SC + 0x04) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 8 : mword 6) ('b"000")), Regidx (mword_of_int 8), sp, 8)) cdec_e0a2 exec_execute_C_SDSP. Qed.

  Lemma schi_06 : kernel_text -∗ instr (mword_of_int (SC + 0x06) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc (SC + 0x06)%Z (mword_of_int 0xfc26 : mword 16)
    (mword_of_int (SC + 0x06) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 7 : mword 6) ('b"000")), Regidx (mword_of_int 9), sp, 8)) cdec_fc26 exec_execute_C_SDSP. Qed.

  Lemma schi_08 : kernel_text -∗ instr (mword_of_int (SC + 0x08) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc (SC + 0x08)%Z (mword_of_int 0xf84a : mword 16)
    (mword_of_int (SC + 0x08) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 6) ('b"000")), Regidx (mword_of_int 18), sp, 8)) cdec_f84a exec_execute_C_SDSP. Qed.

  Lemma schi_0a : kernel_text -∗ instr (mword_of_int (SC + 0x0a) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc (SC + 0x0a)%Z (mword_of_int 0xf44e : mword 16)
    (mword_of_int (SC + 0x0a) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 5 : mword 6) ('b"000")), Regidx (mword_of_int 19), sp, 8)) cdec_f44e exec_execute_C_SDSP. Qed.

  Lemma schi_0c : kernel_text -∗ instr (mword_of_int (SC + 0x0c) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc (SC + 0x0c)%Z (mword_of_int 0xf052 : mword 16)
    (mword_of_int (SC + 0x0c) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 6) ('b"000")), Regidx (mword_of_int 20), sp, 8)) cdec_f052 exec_execute_C_SDSP. Qed.

  Lemma schi_0e : kernel_text -∗ instr (mword_of_int (SC + 0x0e) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc (SC + 0x0e)%Z (mword_of_int 0xec56 : mword 16)
    (mword_of_int (SC + 0x0e) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 3 : mword 6) ('b"000")), Regidx (mword_of_int 21), sp, 8)) cdec_ec56 exec_execute_C_SDSP. Qed.

  Lemma schi_10 : kernel_text -∗ instr (mword_of_int (SC + 0x10) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)).
  Proof. mk_rvc (SC + 0x10)%Z (mword_of_int 0xe85a : mword 16)
    (mword_of_int (SC + 0x10) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 2 : mword 6) ('b"000")), Regidx (mword_of_int 22), sp, 8)) cdec_e85a exec_execute_C_SDSP. Qed.

  Lemma schi_12 : kernel_text -∗ instr (mword_of_int (SC + 0x12) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)).
  Proof. mk_rvc (SC + 0x12)%Z (mword_of_int 0xe45e : mword 16)
    (mword_of_int (SC + 0x12) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 1 : mword 6) ('b"000")), Regidx (mword_of_int 23), sp, 8)) cdec_e45e exec_execute_C_SDSP. Qed.

  Lemma schi_14 : kernel_text -∗ instr (mword_of_int (SC + 0x14) : mword 64) true (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)).
  Proof. mk_rvc (SC + 0x14)%Z (mword_of_int 0xe062 : mword 16)
    (mword_of_int (SC + 0x14) : mword 64) (STORE (zero_extend' 12 (concat_vec (mword_of_int 0 : mword 6) ('b"000")), Regidx (mword_of_int 24), sp, 8)) cdec_e062 exec_execute_C_SDSP. Qed.

  (* ---- +0x16: c.addi4spn s0,sp,80 (the frame pointer) ---- *)
  Lemma schi_16 : kernel_text -∗ instr (mword_of_int (SC + 0x16) : mword 64) true (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc (SC + 0x16)%Z (mword_of_int 0x0880 : mword 16)
    (mword_of_int (SC + 0x16) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 20 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) cdec_0880 exec_execute_C_ADDI4SPN. Qed.

  (* ---- +0x18..+0x1c: c.mv a5,tp / sext.w a5 / slli s6,a5,7 ---- *)
  Lemma schi_18 : kernel_text -∗ instr (mword_of_int (SC + 0x18) : mword 64) true (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)).
  Proof. mk_rvc (SC + 0x18)%Z (mword_of_int 0x8792 : mword 16)
    (mword_of_int (SC + 0x18) : mword 64) (RTYPE (Regidx (mword_of_int 4), zreg, Regidx (mword_of_int 15), ADD)) cdec_8792 exec_execute_C_MV. Qed.

  Lemma schi_1a : kernel_text -∗ instr (mword_of_int (SC + 0x1a) : mword 64) true (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))).
  Proof. mk_rvc (SC + 0x1a)%Z (mword_of_int 0x2781 : mword 16)
    (mword_of_int (SC + 0x1a) : mword 64) (ADDIW (sign_extend' 12 (mword_of_int 0 : mword 6), Regidx (mword_of_int 15), Regidx (mword_of_int 15))) cdec_2781 exec_execute_C_ADDIW. Qed.

  Lemma schi_1c : kernel_text -∗ instr (mword_of_int (SC + 0x1c) : mword 64) false (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 22), SLLI)).
  Proof. mk_base (SC + 0x1c)%Z (mword_of_int 0x00779b13 : mword 32)
    (mword_of_int (SC + 0x1c) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 22), SLLI)) schdec_00779b13. Qed.

  (* ---- +0x20..+0x2a: c->proc = 0 ---- *)
  Lemma schi_20 : kernel_text -∗ instr (mword_of_int (SC + 0x20) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (SC + 0x20)%Z (mword_of_int 0x00010717 : mword 32)
    (mword_of_int (SC + 0x20) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_00010717. Qed.

  Lemma schi_24 : kernel_text -∗ instr (mword_of_int (SC + 0x24) : mword 64) false (ITYPE (mword_of_int 1454 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (SC + 0x24)%Z (mword_of_int 0x5ae70713 : mword 32)
    (mword_of_int (SC + 0x24) : mword 64) (ITYPE (mword_of_int 1454 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) schdec_5ae70713. Qed.

  Lemma schi_28 : kernel_text -∗ instr (mword_of_int (SC + 0x28) : mword 64) true (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)).
  Proof. mk_rvc (SC + 0x28)%Z (mword_of_int 0x975a : mword 16)
    (mword_of_int (SC + 0x28) : mword 64) (RTYPE (Regidx (mword_of_int 22), Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADD)) schdec_975a exec_execute_C_ADD. Qed.

  Lemma schi_2a : kernel_text -∗ instr (mword_of_int (SC + 0x2a) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8)).
  Proof. mk_base (SC + 0x2a)%Z (mword_of_int 0x02073823 : mword 32)
    (mword_of_int (SC + 0x2a) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 14), 8)) schdec_02073823. Qed.

  (* ---- +0x2e..+0x36: s6 = &c->context ---- *)
  Lemma schi_2e : kernel_text -∗ instr (mword_of_int (SC + 0x2e) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)).
  Proof. mk_base (SC + 0x2e)%Z (mword_of_int 0x00010717 : mword 32)
    (mword_of_int (SC + 0x2e) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 14), AUIPC)) bdec_00010717. Qed.

  Lemma schi_32 : kernel_text -∗ instr (mword_of_int (SC + 0x32) : mword 64) false (ITYPE (mword_of_int 1496 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)).
  Proof. mk_base (SC + 0x32)%Z (mword_of_int 0x5d870713 : mword 32)
    (mword_of_int (SC + 0x32) : mword 64) (ITYPE (mword_of_int 1496 : mword 12, Regidx (mword_of_int 14), Regidx (mword_of_int 14), ADDI)) schdec_5d870713. Qed.

  Lemma schi_36 : kernel_text -∗ instr (mword_of_int (SC + 0x36) : mword 64) true (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADD)).
  Proof. mk_rvc (SC + 0x36)%Z (mword_of_int 0x9b3a : mword 16)
    (mword_of_int (SC + 0x36) : mword 64) (RTYPE (Regidx (mword_of_int 14), Regidx (mword_of_int 22), Regidx (mword_of_int 22), ADD)) schdec_9b3a exec_execute_C_ADD. Qed.

  (* ---- +0x38: c.li s8,4 (RUNNING) ---- *)
  Lemma schi_38 : kernel_text -∗ instr (mword_of_int (SC + 0x38) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)).
  Proof. mk_rvc (SC + 0x38)%Z (mword_of_int 0x4c11 : mword 16)
    (mword_of_int (SC + 0x38) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 4 : mword 6), zreg, Regidx (mword_of_int 24), ADDI)) schdec_4c11 exec_execute_C_LI. Qed.

  (* ---- +0x3a..+0x44: s4 = &cpus[cpuid()] ---- *)
  Lemma schi_3a : kernel_text -∗ instr (mword_of_int (SC + 0x3a) : mword 64) true (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)).
  Proof. mk_rvc (SC + 0x3a)%Z (mword_of_int 0x079e : mword 16)
    (mword_of_int (SC + 0x3a) : mword 64) (SHIFTIOP (mword_of_int 7 : mword 6, Regidx (mword_of_int 15), Regidx (mword_of_int 15), SLLI)) cdec_079e exec_execute_C_SLLI. Qed.

  Lemma schi_3c : kernel_text -∗ instr (mword_of_int (SC + 0x3c) : mword 64) false (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 20), AUIPC)).
  Proof. mk_base (SC + 0x3c)%Z (mword_of_int 0x00010a17 : mword 32)
    (mword_of_int (SC + 0x3c) : mword 64) (UTYPE (mword_of_int 0x10 : mword 20, Regidx (mword_of_int 20), AUIPC)) schdec_00010a17. Qed.

  Lemma schi_40 : kernel_text -∗ instr (mword_of_int (SC + 0x40) : mword 64) false (ITYPE (mword_of_int 1426 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)).
  Proof. mk_base (SC + 0x40)%Z (mword_of_int 0x592a0a13 : mword 32)
    (mword_of_int (SC + 0x40) : mword 64) (ITYPE (mword_of_int 1426 : mword 12, Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADDI)) schdec_592a0a13. Qed.

  Lemma schi_44 : kernel_text -∗ instr (mword_of_int (SC + 0x44) : mword 64) true (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc (SC + 0x44)%Z (mword_of_int 0x9a3e : mword 16)
    (mword_of_int (SC + 0x44) : mword 64) (RTYPE (Regidx (mword_of_int 15), Regidx (mword_of_int 20), Regidx (mword_of_int 20), ADD)) schdec_9a3e exec_execute_C_ADD. Qed.

  (* ---- +0x46: c.li s7,1 ---- *)
  Lemma schi_46 : kernel_text -∗ instr (mword_of_int (SC + 0x46) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)).
  Proof. mk_rvc (SC + 0x46)%Z (mword_of_int 0x4b85 : mword 16)
    (mword_of_int (SC + 0x46) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 1 : mword 6), zreg, Regidx (mword_of_int 23), ADDI)) cdec_4b85 exec_execute_C_LI. Qed.

  (* ---- +0x48: c.j +0x86 (jump into the loop head) ---- *)
  Lemma schi_48 : kernel_text -∗ instr (mword_of_int (SC + 0x48) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SC + 0x48)%Z (mword_of_int 0xa83d : mword 16)
    (mword_of_int (SC + 0x48) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 31 : mword 11) ('b"0")), zreg)) schdec_a83d exec_execute_C_J. Qed.

  (* ---- +0x4a..+0x54: release(&p->lock); p++; done? ---- *)
  Lemma schi_4a : kernel_text -∗ instr (mword_of_int (SC + 0x4a) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SC + 0x4a)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SC + 0x4a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma schi_4c : kernel_text -∗ instr (mword_of_int (SC + 0x4c) : mword 64) false (JAL (mword_of_int 2092746 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x4c)%Z (mword_of_int 0xecbfe0ef : mword 32)
    (mword_of_int (SC + 0x4c) : mword 64) (JAL (mword_of_int 2092746 : mword 21, Regidx (mword_of_int 1))) schdec_ecbfe0ef. Qed.

  Lemma schi_50 : kernel_text -∗ instr (mword_of_int (SC + 0x50) : mword 64) false (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (SC + 0x50)%Z (mword_of_int 0x16848493 : mword 32)
    (mword_of_int (SC + 0x50) : mword 64) (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) bdec_16848493. Qed.

  Lemma schi_54 : kernel_text -∗ instr (mword_of_int (SC + 0x54) : mword 64) false (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)).
  Proof. mk_base (SC + 0x54)%Z (mword_of_int 0x03248563 : mword 32)
    (mword_of_int (SC + 0x54) : mword 64) (BTYPE (mword_of_int 42 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ)) schdec_03248563. Qed.

  (* ---- +0x58..+0x60: acquire(&p->lock); p->state == RUNNABLE? ---- *)
  Lemma schi_58 : kernel_text -∗ instr (mword_of_int (SC + 0x58) : mword 64) true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SC + 0x58)%Z (mword_of_int 0x8526 : mword 16)
    (mword_of_int (SC + 0x58) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) cdec_8526 exec_execute_C_MV. Qed.

  Lemma schi_5a : kernel_text -∗ instr (mword_of_int (SC + 0x5a) : mword 64) false (JAL (mword_of_int 2092596 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x5a)%Z (mword_of_int 0xe35fe0ef : mword 32)
    (mword_of_int (SC + 0x5a) : mword 64) (JAL (mword_of_int 2092596 : mword 21, Regidx (mword_of_int 1))) schdec_e35fe0ef. Qed.

  Lemma schi_5e : kernel_text -∗ instr (mword_of_int (SC + 0x5e) : mword 64) true (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)).
  Proof. mk_rvc (SC + 0x5e)%Z (mword_of_int 0x4c9c : mword 16)
    (mword_of_int (SC + 0x5e) : mword 64) (LOAD (mword_of_int 24, Regidx (mword_of_int 9), Regidx (mword_of_int 15), false, 4)) cdec_4c9c cexec_lw24_s1_a5. Qed.

  Lemma schi_60 : kernel_text -∗ instr (mword_of_int (SC + 0x60) : mword 64) false (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (SC + 0x60)%Z (mword_of_int 0xff3795e3 : mword 32)
    (mword_of_int (SC + 0x60) : mword 64) (BTYPE (mword_of_int 8170 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)) schdec_ff3795e3. Qed.

  (* ---- +0x64..+0x72: p->state = RUNNING; c->proc = p; swtch ---- *)
  Lemma schi_64 : kernel_text -∗ instr (mword_of_int (SC + 0x64) : mword 64) false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (SC + 0x64)%Z (mword_of_int 0x0184ac23 : mword 32)
    (mword_of_int (SC + 0x64) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 24), Regidx (mword_of_int 9), 4)) schdec_0184ac23. Qed.

  Lemma schi_68 : kernel_text -∗ instr (mword_of_int (SC + 0x68) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 20), 8)).
  Proof. mk_base (SC + 0x68)%Z (mword_of_int 0x029a3823 : mword 32)
    (mword_of_int (SC + 0x68) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 20), 8)) schdec_029a3823. Qed.

  Lemma schi_6c : kernel_text -∗ instr (mword_of_int (SC + 0x6c) : mword 64) false (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI)).
  Proof. mk_base (SC + 0x6c)%Z (mword_of_int 0x06048593 : mword 32)
    (mword_of_int (SC + 0x6c) : mword 64) (ITYPE (mword_of_int 96 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 11), ADDI)) schdec_06048593. Qed.

  Lemma schi_70 : kernel_text -∗ instr (mword_of_int (SC + 0x70) : mword 64) true (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc (SC + 0x70)%Z (mword_of_int 0x855a : mword 16)
    (mword_of_int (SC + 0x70) : mword 64) (RTYPE (Regidx (mword_of_int 22), zreg, Regidx (mword_of_int 10), ADD)) cdec_855a exec_execute_C_MV. Qed.

  Lemma schi_72 : kernel_text -∗ instr (mword_of_int (SC + 0x72) : mword 64) false (JAL (mword_of_int 1452 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (SC + 0x72)%Z (mword_of_int 0x5ac000ef : mword 32)
    (mword_of_int (SC + 0x72) : mword 64) (JAL (mword_of_int 1452 : mword 21, Regidx (mword_of_int 1))) schdec_5ac000ef. Qed.

  (* ---- +0x76..+0x7c: c->proc = 0; found = 1; loop ---- *)
  Lemma schi_76 : kernel_text -∗ instr (mword_of_int (SC + 0x76) : mword 64) false (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 20), 8)).
  Proof. mk_base (SC + 0x76)%Z (mword_of_int 0x020a3823 : mword 32)
    (mword_of_int (SC + 0x76) : mword 64) (STORE (mword_of_int 48 : mword 12, Regidx (mword_of_int 0), Regidx (mword_of_int 20), 8)) schdec_020a3823. Qed.

  Lemma schi_7a : kernel_text -∗ instr (mword_of_int (SC + 0x7a) : mword 64) true (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 21), ADD)).
  Proof. mk_rvc (SC + 0x7a)%Z (mword_of_int 0x8ade : mword 16)
    (mword_of_int (SC + 0x7a) : mword 64) (RTYPE (Regidx (mword_of_int 23), zreg, Regidx (mword_of_int 21), ADD)) schdec_8ade exec_execute_C_MV. Qed.

  Lemma schi_7c : kernel_text -∗ instr (mword_of_int (SC + 0x7c) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SC + 0x7c)%Z (mword_of_int 0xb7f9 : mword 16)
    (mword_of_int (SC + 0x7c) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2023 : mword 11) ('b"0")), zreg)) schdec_b7f9 exec_execute_C_J. Qed.

  (* ---- +0x7e..+0x82: if (!found) wfi ---- *)
  Lemma schi_7e : kernel_text -∗ instr (mword_of_int (SC + 0x7e) : mword 64) false (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BNE)).
  Proof. mk_base (SC + 0x7e)%Z (mword_of_int 0x000a9463 : mword 32)
    (mword_of_int (SC + 0x7e) : mword 64) (BTYPE (mword_of_int 8 : mword 13, Regidx (mword_of_int 0), Regidx (mword_of_int 21), BNE)) schdec_000a9463. Qed.

  Lemma schi_82 : kernel_text -∗ instr (mword_of_int (SC + 0x82) : mword 64) false (WFI tt).
  Proof. mk_base (SC + 0x82)%Z (mword_of_int 0x10500073 : mword 32)
    (mword_of_int (SC + 0x82) : mword 64) (WFI tt) schdec_10500073. Qed.

  (* ---- +0x86..+0x8a: the loop head's intr_on / intr_off ---- *)
  Lemma schi_86 : kernel_text -∗ instr (mword_of_int (SC + 0x86) : mword 64) false (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRS)).
  Proof. mk_base (SC + 0x86)%Z (mword_of_int 0x10016073 : mword 32)
    (mword_of_int (SC + 0x86) : mword 64) (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRS)) bdec_10016073. Qed.

  Lemma schi_8a : kernel_text -∗ instr (mword_of_int (SC + 0x8a) : mword 64) false (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRC)).
  Proof. mk_base (SC + 0x8a)%Z (mword_of_int 0x10017073 : mword 32)
    (mword_of_int (SC + 0x8a) : mword 64) (CSRImm (Ox"100", mword_of_int 2, Regidx (mword_of_int 0), CSRRC)) schdec_10017073. Qed.

  (* ---- +0x8e..+0xa2: found = 0; p = proc; RUNNABLE; limit = &proc[NPROC] ---- *)
  Lemma schi_8e : kernel_text -∗ instr (mword_of_int (SC + 0x8e) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc (SC + 0x8e)%Z (mword_of_int 0x4a81 : mword 16)
    (mword_of_int (SC + 0x8e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 0 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)) schdec_4a81 exec_execute_C_LI. Qed.

  Lemma schi_90 : kernel_text -∗ instr (mword_of_int (SC + 0x90) : mword 64) false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (SC + 0x90)%Z (mword_of_int 0x00011497 : mword 32)
    (mword_of_int (SC + 0x90) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)) bdec_00011497. Qed.

  Lemma schi_94 : kernel_text -∗ instr (mword_of_int (SC + 0x94) : mword 64) false (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (SC + 0x94)%Z (mword_of_int 0x96e48493 : mword 32)
    (mword_of_int (SC + 0x94) : mword 64) (ITYPE (mword_of_int 2414 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) schdec_96e48493. Qed.

  Lemma schi_98 : kernel_text -∗ instr (mword_of_int (SC + 0x98) : mword 64) true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc (SC + 0x98)%Z (mword_of_int 0x498d : mword 16)
    (mword_of_int (SC + 0x98) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) schdec_498d exec_execute_C_LI. Qed.

  Lemma schi_9a : kernel_text -∗ instr (mword_of_int (SC + 0x9a) : mword 64) false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (SC + 0x9a)%Z (mword_of_int 0x00016917 : mword 32)
    (mword_of_int (SC + 0x9a) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)) bdec_00016917. Qed.

  Lemma schi_9e : kernel_text -∗ instr (mword_of_int (SC + 0x9e) : mword 64) false (ITYPE (mword_of_int 868 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (SC + 0x9e)%Z (mword_of_int 0x36490913 : mword 32)
    (mword_of_int (SC + 0x9e) : mword 64) (ITYPE (mword_of_int 868 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) schdec_36490913. Qed.

  (* ---- +0xa2: c.j -0x4a (back to the acquire at +0x58) ---- *)
  Lemma schi_a2 : kernel_text -∗ instr (mword_of_int (SC + 0xa2) : mword 64) true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc (SC + 0xa2)%Z (mword_of_int 0xbf5d : mword 16)
    (mword_of_int (SC + 0xa2) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2011 : mword 11) ('b"0")), zreg)) schdec_bf5d exec_execute_C_J. Qed.

End CodeScheduler.

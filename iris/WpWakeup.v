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
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import InstrBytes MinstretInv RiscvFetchExec WpGpr WpEntryNew.
Require Import WpLock.
Require Import WpGprAddi WpGprRvc WpGprLoad WpGprStore.
Require Import WpSmodeGpr WpMemsetS WpPushOff WpPushOffMem VcGenS.
Require Import WpAcquireLock WpRelease.
Require Import WpSwtchVc.
Require Import RiscvExec RiscvExtras RiscvTryStep WpDecode WpFetch WpLeafCommon WpRvcBridge WpKallocDecode.
From Kernel Require Import KernelSyms KernelInstrs.
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
Lemma wkd_f58 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00011497 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f5c addi s1,s1,-2016 *)
Lemma wkd_f5c s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x82048493 : mword 32)) s
  = Some (ITYPE (mword_of_int 2080 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f64 auipc s2,0x16 *)
Lemma wkd_f64 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x00016917 : mword 32)) s
  = Some (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f68 addi s2,s2,532 *)
Lemma wkd_f68 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x21490913 : mword 32)) s
  = Some (ITYPE (mword_of_int 532 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f74 addi s1,s1,360 *)
Lemma wkd_f74 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x16848493 : mword 32)) s
  = Some (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f78 beq s1,s2,+36 *)
Lemma wkd_f78 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x03248263 : mword 32)) s
  = Some (BTYPE (mword_of_int 36 : mword 13, Regidx (mword_of_int 18), Regidx (mword_of_int 9), BEQ), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f80 beq a0,s1,-12 *)
Lemma wkd_f80 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xfe950ae3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8180 : mword 13, Regidx (mword_of_int 9), Regidx (mword_of_int 10), BEQ), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f8c bne a5,s3,-30 *)
Lemma wkd_f8c s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xff3791e3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f92 bne a5,s4,-36 *)
Lemma wkd_f92 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xfd479ee3 : mword 32)) s
  = Some (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f96 sw s5,24(s1) *)
Lemma wkd_f96 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x0154ac23 : mword 32)) s
  = Some (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f70 jal release (-4846) *)
Lemma wkd_f70 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xd13fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092306 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f7c jal myproc (-1670) *)
Lemma wkd_f7c s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0x97bff0ef : mword 32)) s
  = Some (JAL (mword_of_int 2095482 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.
(* 0x80001f86 jal acquire (-5004) *)
Lemma wkd_f86 s : priv_mSU (register_lookup cur_privilege (sregs s)) = true ->
  exec (ext_decode (mword_of_int 0xc75fe0ef : mword 32)) s
  = Some (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1)), s).
Proof. intro Hpriv. decode_any s Hpriv. Qed.

(* ---- compressed instructions (misa.C + rvc_oneshot; ext_decode_compressed) ---- *)
(* 0x80001f44 c.addi16sp sp,-64 *)
Lemma wkd_f44 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7139 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 60 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001faa c.addi16sp sp,64 *)
Lemma wkd_faa s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6121 : mword 16)) s
  = Some (C_ADDI16SP (mword_of_int 4 : mword 6), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f46..52 c.sdsp ra/s0/s1/s2/s3/s4/s5 at 56/48/40/32/24/16/8(sp) *)
Lemma wkd_f46 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xfc06 : mword 16)) s
  = Some (C_SDSP (mword_of_int 7, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f48 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf822 : mword 16)) s
  = Some (C_SDSP (mword_of_int 6, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f4a s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf426 : mword 16)) s
  = Some (C_SDSP (mword_of_int 5, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f4c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xf04a : mword 16)) s
  = Some (C_SDSP (mword_of_int 4, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f4e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xec4e : mword 16)) s
  = Some (C_SDSP (mword_of_int 3, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f50 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe852 : mword 16)) s
  = Some (C_SDSP (mword_of_int 2, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f52 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0xe456 : mword 16)) s
  = Some (C_SDSP (mword_of_int 1, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f54 c.addi4spn s0,sp,64 *)
Lemma wkd_f54 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x0080 : mword 16)) s
  = Some (C_ADDI4SPN (Cregidx (mword_of_int 0), mword_of_int 16), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f56 c.mv s4,a0 *)
Lemma wkd_f56 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8a2a : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 20), Regidx (mword_of_int 10)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001f6e / 0x80001f84 c.mv a0,s1 *)
Lemma wkd_f6e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8526 : mword 16)) s
  = Some (C_MV (Regidx (mword_of_int 10), Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.
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
(* 0x80001f9c..a8 c.ldsp ra/s0/s1/s2/s3/s4/s5 at 56/48/40/32/24/16/8(sp) *)
Lemma wkd_f9c s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x70e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 7, Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_f9e s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7442 : mword 16)) s
  = Some (C_LDSP (mword_of_int 6, Regidx (mword_of_int 8)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_fa0 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x74a2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 5, Regidx (mword_of_int 9)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_fa2 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x7902 : mword 16)) s
  = Some (C_LDSP (mword_of_int 4, Regidx (mword_of_int 18)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_fa4 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x69e2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 3, Regidx (mword_of_int 19)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_fa6 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6a42 : mword 16)) s
  = Some (C_LDSP (mword_of_int 2, Regidx (mword_of_int 20)), s).
Proof. intro H. rvc_oneshot s H. Qed.
Lemma wkd_fa8 s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x6aa2 : mword 16)) s
  = Some (C_LDSP (mword_of_int 1, Regidx (mword_of_int 21)), s).
Proof. intro H. rvc_oneshot s H. Qed.
(* 0x80001fac c.ret = c.jr ra *)
Lemma wkd_fac s : eq_vec (_get_Misa_C (register_lookup misa s.(sregs))) ('b"1") = true ->
  exec (ext_decode_compressed (mword_of_int 0x8082 : mword 16)) s
  = Some (C_JR (Regidx (mword_of_int 1)), s).
Proof. intro H. rvc_oneshot s H. Qed.

(* C_LW ExecuteAs bridge (no generic one in WpGprRvc; mirrors exec_execute_C_LD). *)
Lemma wkx_clw (uimm : mword 5) (rsc rdc : cregidx) s :
  exec (execute (C_LW (uimm, rsc, rdc))) s
  = Some (ExecuteAs (LOAD (zero_extend' 12 (concat_vec uimm ('b"00")),
                           creg2reg_idx rsc, creg2reg_idx rdc, false, 4)), s).
Proof. unfold execute. cbn match. unfold execute_C_LW. cbn zeta. apply exec_returnM. Qed.


(* ===================================================================== *)
(* struct proc geometry (parameter-free; used by the myproc axiom and the *)
(* invariant/proof below).                                                *)
(* ===================================================================== *)
  (* ---- struct proc geometry ---- *)
  Definition NPROC : nat := 64%nat.
  Definition proc_size : Z := 360.
  Definition proc_base : mword 64 := mword_of_int KernelSyms.proc.
  Definition proc_addr (i : nat) : mword 64 :=
    add_vec proc_base (mword_of_int (proc_size * Z.of_nat i)).

  Definition state_off : Z := 24.
  Definition chan_off : Z := 32.
  Definition context_off : Z := 96.

  Definition p_state (pa : mword 64) : mword 64 := add_vec pa (mword_of_int state_off).
  Definition p_chan (pa : mword 64) : mword 64 := add_vec pa (mword_of_int chan_off).
  Definition p_context (pa : mword 64) : mword 64 := add_vec pa (mword_of_int context_off).

  (* enum procstate codes (kernel/proc.h): UNUSED=0 USED=1 SLEEPING=2
     RUNNABLE=3 RUNNING=4 ZOMBIE=5. *)
  Definition SLEEPING : mword 32 := mword_of_int 2.
  Definition RUNNABLE : mword 32 := mword_of_int 3.

  (* A state that requires the [valid_context] obligation: the two "parked"
     states that own a saved context reachable by swtch. *)
  Definition needs_ctx (st : mword 32) : bool :=
    bool_decide (st = RUNNABLE) || bool_decide (st = SLEEPING).

Section WkLeaves.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* c.li rd, imm  ==  addi rd, x0, sext(imm) : writes sext(imm) into rd.
     Mirrors wp_caddi_gpr_s_config but with rs1 = x0 (so the value is the
     immediate, not rd+imm).  Discharged through wp_gpr_write_s_config. *)
  Lemma wp_cli_gpr_s_config (root_ppn : mword 44) E (Φ : mval -> iProp Σ)
      (pc : mword 64) (rd : mword 5) (imm : mword 6)
      (m : gmap regidx (mword 64))
      (mstatus0 mie_v mdv0 menvcfg0 : mword 64)
      {dq : dfrac} :
    ↑minstretN ⊆ E ->
    eq_vec (_get_Mstatus_SIE mstatus0) ('b"1") = false ->
    eq_vec (_get_Mstatus_MPRV mstatus0) ('b"1") = false ->
    _get_Mstatus_SXL mstatus0 = 'b"10" ->
    and_vec mie_v (not_vec mdv0) = zeros' 64 ->
    eq_vec (_get_MEnvcfg_PBMTE menvcfg0) ('b"0") = true ->
    uint rd <> 0 ->
    hw_config -∗ minstret_inv -∗
    hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
    cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
    mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
    tlb_inv root_ppn -∗
    pc_is pc -∗ gpr_file m -∗
    instr pc true (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI)) -∗
    ( hart_state ↦ᵣ{ dq } HART_ACTIVE tt -∗
      cur_privilege ↦ᵣ{ dq } Supervisor -∗ mstatus ↦ᵣ{ dq } mstatus0 -∗
      mie ↦ᵣ{ dq } mie_v -∗ mideleg ↦ᵣ{ dq } mdv0 -∗ menvcfg ↦ᵣ{ dq } menvcfg0 -∗
      tlb_inv root_ppn -∗
      pc_is (add_vec_int pc 2) -∗
      gpr_file (<[Regidx rd := regval_into_reg
        (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))]> m) -∗
      WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hrd
              _
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont").
    intros s_pc Hnpc Hva _.
    change zreg with (Regidx (zero_extend' 5 ('b"00") : mword 5)).
    rewrite (exec_execute_ITYPE_ADDI_gpr (zero_extend' 5 ('b"00")) rd
               (sign_extend' 12 imm) s_pc).
    replace (Z.eqb (uint rd) 0) with false by (symmetry; apply Z.eqb_neq; exact Hrd).
    unfold gpr_addi_val.
    replace (Z.eqb (uint (zero_extend' 5 ('b"00") : mword 5)) 0) with true
      by (vm_compute; reflexivity).
    reflexivity.
  Qed.

  (* ---- instruction fact builders (verbatim from WpSwtchVc) ---- *)
  Local Ltac mk_rvc4 A h w pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hsub := fresh "Hsub" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = true) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hsub : subrange_vec_dec w 15 0 = h) by (apply bv_eq; vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc4 pc h w H2al H4al Hrvc Hsub);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_rvc2 A h pc ast decname expname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let H4al := fresh "H4al" in let Hrvc := fresh "Hrvc" in
    let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (H4al : is_aligned_vaddr (Virtaddr pc) 4 = false) by (vm_compute; reflexivity);
    assert (Hrvc : isRVC h = true) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 2)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte h j))
      by (intros j Hj;
          do 2 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_RVC h);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_rvc2 pc h H2al H4al Hrvc);
      iApply (kernel_window_pc A h 2 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; cbn [fetch_is_rvc];
      eexists; (split; [ apply decname; assumption
                       | split; [ vm_compute; reflexivity
                                | intro; apply expname ] ]) ].

  Local Ltac mk_base A w pc ast decname :=
    let Hlpad := fresh "Hlpad" in let H2al := fresh "H2al" in
    let Hnrvc := fresh "Hnrvc" in let Hbytes := fresh "Hbytes" in
    assert (Hlpad : is_lpad_instruction ast = false) by (vm_compute; reflexivity);
    assert (H2al : is_aligned_vaddr (Virtaddr pc) 2 = true) by (vm_compute; reflexivity);
    assert (Hnrvc : isRVC (subrange_vec_dec w 15 0) = false) by (vm_compute; reflexivity);
    assert (Hbytes : forall j, (j < 4)%nat ->
        KernelInstrs.kernel_bytes !! (A + Z.of_nat j)%Z = Some (nth_byte w j))
      by (intros j Hj;
          do 4 (destruct j as [|j]; [vm_compute; f_equal; apply bv_eq; reflexivity|]); lia);
    iIntros "#Ht"; rewrite /instr;
    iSplitR; [iPureIntro; exact Hlpad|];
    iExists (F_Base w);
    iSplitR; [iPureIntro; reflexivity|];
    iSplitL "";
    [ iApply (instr_bytes_base pc w H2al Hnrvc);
      iApply (kernel_window_pc A w 4 pc eq_refl Hbytes with "Ht")
    | iIntros (?) "_"; iPureIntro; intros; apply decname; assumption ].

  Local Notation WKI off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.wakeup + off) : mword 64) rvc ast).
  Local Notation csdsp_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 6) ('b"000"))).
  Local Notation cld_imm u :=
    (zero_extend' 12 (concat_vec (mword_of_int u : mword 5) ('b"000"))).

  (* ---- prologue ---- *)
  Lemma wki_00 : WKI 0x00 true (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x00)%Z (mword_of_int 0x7139 : mword 16) (mword_of_int 0xfc067139 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x00) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 60 : mword 6), sp, sp, ADDI)) wkd_f44 exec_execute_C_ADDI16SP. Qed.
  Lemma wki_02 : WKI 0x02 true (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x02)%Z (mword_of_int 0xfc06 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x02) : mword 64) (STORE (csdsp_imm 7, Regidx (mword_of_int 1), sp, 8)) wkd_f46 exec_execute_C_SDSP. Qed.
  Lemma wki_04 : WKI 0x04 true (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x04)%Z (mword_of_int 0xf822 : mword 16) (mword_of_int 0xf426f822 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x04) : mword 64) (STORE (csdsp_imm 6, Regidx (mword_of_int 8), sp, 8)) wkd_f48 exec_execute_C_SDSP. Qed.
  Lemma wki_06 : WKI 0x06 true (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x06)%Z (mword_of_int 0xf426 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x06) : mword 64) (STORE (csdsp_imm 5, Regidx (mword_of_int 9), sp, 8)) wkd_f4a exec_execute_C_SDSP. Qed.
  Lemma wki_08 : WKI 0x08 true (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x08)%Z (mword_of_int 0xf04a : mword 16) (mword_of_int 0xec4ef04a : mword 32) (mword_of_int (KernelSyms.wakeup + 0x08) : mword 64) (STORE (csdsp_imm 4, Regidx (mword_of_int 18), sp, 8)) wkd_f4c exec_execute_C_SDSP. Qed.
  Lemma wki_0a : WKI 0x0a true (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x0a)%Z (mword_of_int 0xec4e : mword 16) (mword_of_int (KernelSyms.wakeup + 0x0a) : mword 64) (STORE (csdsp_imm 3, Regidx (mword_of_int 19), sp, 8)) wkd_f4e exec_execute_C_SDSP. Qed.
  Lemma wki_0c : WKI 0x0c true (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x0c)%Z (mword_of_int 0xe852 : mword 16) (mword_of_int 0xe456e852 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x0c) : mword 64) (STORE (csdsp_imm 2, Regidx (mword_of_int 20), sp, 8)) wkd_f50 exec_execute_C_SDSP. Qed.
  Lemma wki_0e : WKI 0x0e true (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x0e)%Z (mword_of_int 0xe456 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x0e) : mword 64) (STORE (csdsp_imm 1, Regidx (mword_of_int 21), sp, 8)) wkd_f52 exec_execute_C_SDSP. Qed.
  Lemma wki_10 : WKI 0x10 true (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x10)%Z (mword_of_int 0x0080 : mword 16) (mword_of_int 0x8a2a0080 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x10) : mword 64) (ITYPE (caddi4spn_imm (mword_of_int 16 : mword 8), sp, creg2reg_idx (Cregidx (mword_of_int 0)), ADDI)) wkd_f54 exec_execute_C_ADDI4SPN. Qed.
  Lemma wki_12 : WKI 0x12 true (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x12)%Z (mword_of_int 0x8a2a : mword 16) (mword_of_int (KernelSyms.wakeup + 0x12) : mword 64) (RTYPE (Regidx (mword_of_int 10), zreg, Regidx (mword_of_int 20), ADD)) wkd_f56 exec_execute_C_MV. Qed.
  Lemma wki_14 : WKI 0x14 false (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)).
  Proof. mk_base (KernelSyms.wakeup + 0x14)%Z (mword_of_int 0x00011497 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x14) : mword 64) (UTYPE (mword_of_int 0x11 : mword 20, Regidx (mword_of_int 9), AUIPC)) wkd_f58. Qed.
  Lemma wki_18 : WKI 0x18 false (ITYPE (mword_of_int 2080 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)).
  Proof. mk_base (KernelSyms.wakeup + 0x18)%Z (mword_of_int 0x82048493 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x18) : mword 64) (ITYPE (mword_of_int 2080 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI)) wkd_f5c. Qed.
  Lemma wki_1c : WKI 0x1c true (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x1c)%Z (mword_of_int 0x4989 : mword 16) (mword_of_int 0x4a8d4989 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x1c) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 2 : mword 6), zreg, Regidx (mword_of_int 19), ADDI)) wkd_f60 exec_execute_C_LI. Qed.
  Lemma wki_1e : WKI 0x1e true (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x1e)%Z (mword_of_int 0x4a8d : mword 16) (mword_of_int (KernelSyms.wakeup + 0x1e) : mword 64) (ITYPE (sign_extend' 12 (mword_of_int 3 : mword 6), zreg, Regidx (mword_of_int 21), ADDI)) wkd_f62 exec_execute_C_LI. Qed.
  Lemma wki_20 : WKI 0x20 false (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)).
  Proof. mk_base (KernelSyms.wakeup + 0x20)%Z (mword_of_int 0x00016917 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x20) : mword 64) (UTYPE (mword_of_int 0x16 : mword 20, Regidx (mword_of_int 18), AUIPC)) wkd_f64. Qed.
  Lemma wki_24 : WKI 0x24 false (ITYPE (mword_of_int 532 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)).
  Proof. mk_base (KernelSyms.wakeup + 0x24)%Z (mword_of_int 0x21490913 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x24) : mword 64) (ITYPE (mword_of_int 532 : mword 12, Regidx (mword_of_int 18), Regidx (mword_of_int 18), ADDI)) wkd_f68. Qed.
  Lemma wki_28 : WKI 0x28 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x28)%Z (mword_of_int 0xa801 : mword 16) (mword_of_int 0x8526a801 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x28) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0")), zreg)) wkd_f6c exec_execute_C_J. Qed.
  (* ---- loop / release path ---- *)
  Lemma wki_2a : WKI 0x2a true (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x2a)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) wkd_f6e exec_execute_C_MV. Qed.
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
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x40)%Z (mword_of_int 0x8526 : mword 16) (mword_of_int 0xe0ef8526 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) (RTYPE (Regidx (mword_of_int 9), zreg, Regidx (mword_of_int 10), ADD)) wkd_f6e exec_execute_C_MV. Qed.
  Lemma wki_42 : WKI 0x42 false (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1))).
  Proof. mk_base (KernelSyms.wakeup + 0x42)%Z (mword_of_int 0xc75fe0ef : mword 32) (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) (JAL (mword_of_int 2092148 : mword 21, Regidx (mword_of_int 1))) wkd_f86. Qed.
  Lemma wki_46 : WKI 0x46 true (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x46)%Z (mword_of_int 0x4c9c : mword 16) (mword_of_int (KernelSyms.wakeup + 0x46) : mword 64) (LOAD (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")), creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 4)) wkd_f8a wkx_clw. Qed.
  Lemma wki_48 : WKI 0x48 false (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.wakeup + 0x48)%Z (mword_of_int 0xff3791e3 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) (BTYPE (mword_of_int 8162 : mword 13, Regidx (mword_of_int 19), Regidx (mword_of_int 15), BNE)) wkd_f8c. Qed.
  Lemma wki_4c : WKI 0x4c true (LOAD (cld_imm 4, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x4c)%Z (mword_of_int 0x709c : mword 16) (mword_of_int 0x9ee3709c : mword 32) (mword_of_int (KernelSyms.wakeup + 0x4c) : mword 64) (LOAD (cld_imm 4, creg2reg_idx (Cregidx (mword_of_int 1)), creg2reg_idx (Cregidx (mword_of_int 7)), false, 8)) wkd_f90 exec_execute_C_LD. Qed.
  Lemma wki_4e : WKI 0x4e false (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE)).
  Proof. mk_base (KernelSyms.wakeup + 0x4e)%Z (mword_of_int 0xfd479ee3 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) (BTYPE (mword_of_int 8156 : mword 13, Regidx (mword_of_int 20), Regidx (mword_of_int 15), BNE)) wkd_f92. Qed.
  Lemma wki_52 : WKI 0x52 false (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4)).
  Proof. mk_base (KernelSyms.wakeup + 0x52)%Z (mword_of_int 0x0154ac23 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64) (STORE (mword_of_int 24 : mword 12, Regidx (mword_of_int 21), Regidx (mword_of_int 9), 4)) wkd_f96. Qed.
  Lemma wki_56 : WKI 0x56 true (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x56)%Z (mword_of_int 0xbfd1 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x56) : mword 64) (JAL (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0")), zreg)) wkd_f9a exec_execute_C_J. Qed.
  (* ---- epilogue ---- *)
  Lemma wki_58 : WKI 0x58 true (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x58)%Z (mword_of_int 0x70e2 : mword 16) (mword_of_int 0x744270e2 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x58) : mword 64) (LOAD (csdsp_imm 7, sp, Regidx (mword_of_int 1), false, 8)) wkd_f9c exec_execute_C_LDSP. Qed.
  Lemma wki_5a : WKI 0x5a true (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x5a)%Z (mword_of_int 0x7442 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x5a) : mword 64) (LOAD (csdsp_imm 6, sp, Regidx (mword_of_int 8), false, 8)) wkd_f9e exec_execute_C_LDSP. Qed.
  Lemma wki_5c : WKI 0x5c true (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x5c)%Z (mword_of_int 0x74a2 : mword 16) (mword_of_int 0x790274a2 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x5c) : mword 64) (LOAD (csdsp_imm 5, sp, Regidx (mword_of_int 9), false, 8)) wkd_fa0 exec_execute_C_LDSP. Qed.
  Lemma wki_5e : WKI 0x5e true (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x5e)%Z (mword_of_int 0x7902 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x5e) : mword 64) (LOAD (csdsp_imm 4, sp, Regidx (mword_of_int 18), false, 8)) wkd_fa2 exec_execute_C_LDSP. Qed.
  Lemma wki_60 : WKI 0x60 true (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x60)%Z (mword_of_int 0x69e2 : mword 16) (mword_of_int 0x6a4269e2 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x60) : mword 64) (LOAD (csdsp_imm 3, sp, Regidx (mword_of_int 19), false, 8)) wkd_fa4 exec_execute_C_LDSP. Qed.
  Lemma wki_62 : WKI 0x62 true (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x62)%Z (mword_of_int 0x6a42 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x62) : mword 64) (LOAD (csdsp_imm 2, sp, Regidx (mword_of_int 20), false, 8)) wkd_fa6 exec_execute_C_LDSP. Qed.
  Lemma wki_64 : WKI 0x64 true (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x64)%Z (mword_of_int 0x6aa2 : mword 16) (mword_of_int 0x61216aa2 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x64) : mword 64) (LOAD (csdsp_imm 1, sp, Regidx (mword_of_int 21), false, 8)) wkd_fa8 exec_execute_C_LDSP. Qed.
  Lemma wki_66 : WKI 0x66 true (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)).
  Proof. mk_rvc2 (KernelSyms.wakeup + 0x66)%Z (mword_of_int 0x6121 : mword 16) (mword_of_int (KernelSyms.wakeup + 0x66) : mword 64) (ITYPE (caddi16sp_imm (mword_of_int 4 : mword 6), sp, sp, ADDI)) wkd_faa exec_execute_C_ADDI16SP. Qed.
  Lemma wki_68 : WKI 0x68 true (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
  Proof. mk_rvc4 (KernelSyms.wakeup + 0x68)%Z (mword_of_int 0x8082 : mword 16) (mword_of_int 0x71798082 : mword 32) (mword_of_int (KernelSyms.wakeup + 0x68) : mword 64) (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) wkd_fac exec_execute_C_JR. Qed.

End WkLeaves.

(* ======================================================================= *)
(* myproc(), axiomatized.                                                    *)
(*                                                                           *)
(* wakeup only relies on ONE fact about myproc(): the pointer it returns (in *)
(* a0, used to skip the current process) is a genuine entry of the global    *)
(* proc[] table.  We assume a jal-callable whole-function WP that: returns   *)
(* a0 = proc_addr j for some j < NPROC; preserves the callee-saved registers *)
(* (sp, s0..s11); and preserves the ambient config [smode_config γc], its    *)
(* SIE ghost half, and [tlb_inv] -- exactly the resources acquire/release     *)
(* thread -- with myproc managing its own stack frame internally.  (For now,  *)
(* it just returns some proc.)                                                *)
(* ======================================================================= *)
Axiom wp_myproc :
  forall {Σ : gFunctors} {HR : riscvGS Σ} {HS : sieG Σ} {CID : CpuId}
    (root_ppn : mword 44) (E : coPset) (Phi : mval -> iProp Σ)
    (γc : gname) (bsie : mword 1)
    (m : gmap regidx (mword 64)),
    ↑minstretN ⊆ E ->
    let ret_tgt :=
      update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                        (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.myproc) -∗ gpr_file m -∗
    (∀ (j : nat) (mret : gmap regidx (mword 64)),
       ⌜(j < NPROC)%nat⌝ -∗
       ⌜mret !!! Regidx (mword_of_int 10 : mword 5) = proc_addr j⌝ -∗
       ⌜forall r : mword 5,
          r ∈ [mword_of_int 2; mword_of_int 8; mword_of_int 9;
               mword_of_int 18; mword_of_int 19; mword_of_int 20;
               mword_of_int 21; mword_of_int 22; mword_of_int 23;
               mword_of_int 24; mword_of_int 25; mword_of_int 26;
               mword_of_int 27] ->
          mret !!! Regidx r = m !!! Regidx r⌝ -∗
       smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
       pc_is ret_tgt -∗ gpr_file mret -∗
       WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.

(* ======================================================================= *)
(* Leaf lemmas specific to wakeup's instruction mix that were not already   *)
(* available: the compressed [c.li rd, imm] (ADDI from x0).                  *)

Section ProcInv.
  Context `{!riscvGS Σ, !lockG Σ, !sieG Σ}.
  Context `{CID : CpuId}.
  (* the ambient S-mode config a running/resumed kernel thread holds -- the same
     [sconf] (smode_config γc + the SIE ghost half + tlb_inv) that wp_swtch is
     now stated against, so a proc's saved context interoperates with swtch. *)
  Context (root_ppn : mword 44) (E : coPset) (Phi : mval -> iProp Σ).
  Context (γc : gname) (bsie : mword 1) (dq : dfrac).

  Local Notation VC :=
    (valid_context (sconf root_ppn γc bsie dq) E Phi).

  (* [P contains the lock token]: P is an accessor from which the exclusive
     [locked γ] can be borrowed and returned.  (An accessor, not plain
     ownership, so P can carry further per-proc coupling -- "more later".) *)
  Definition contains_lock (γ : gname) (P : mword 64 -d> iPropO Σ) : iProp Σ :=
    (□ ∀ c : mword 64, P c -∗ locked γ ∗ (locked γ -∗ P c))%I.

  Global Instance contains_lock_persistent γ P : Persistent (contains_lock γ P).
  Proof. apply _. Qed.

  (* the [valid_context] obligation attached to a parked proc: some resumer
     predicate P that hands over the lock token, plus a valid saved context at
     [&p->context]. *)
  Definition proc_ctx (γ : gname) (pa : mword 64) : iProp Σ :=
    (∃ P : mword 64 -d> iPropO Σ,
       contains_lock γ P ∗ VC P (p_context pa))%I.

  (* the resource protected by [p->lock]. *)
  Definition proc_lock_res (γ : gname) (pa : mword 64) : iProp Σ :=
    (∃ (st : mword 32) (ch : mword 64),
       p_state pa ↦₄ st ∗
       p_chan pa ↦₈ ch ∗
       (if needs_ctx st then proc_ctx γ pa else emp))%I.

  (* the global proc-array invariant: an [is_lock] over every proc's
     [proc_lock_res]. *)
  Definition procs_inv (γs : list gname) : iProp Σ :=
    (⌜length γs = NPROC⌝ ∗
     [∗ list] i ↦ γ ∈ γs, is_lock γ (proc_addr i) (proc_lock_res γ (proc_addr i)))%I.

  Global Instance procs_inv_persistent γs : Persistent (procs_inv γs).
  Proof. apply _. Qed.

  (* the per-proc [is_lock] extracted from the global invariant. *)
  Lemma procs_inv_lookup (γs : list gname) (i : nat) (γ : gname) :
    γs !! i = Some γ ->
    procs_inv γs -∗ is_lock γ (proc_addr i) (proc_lock_res γ (proc_addr i)).
  Proof.
    iIntros (Hi) "[_ Hbig]".
    by iDestruct (big_sepL_lookup with "Hbig") as "$".
  Qed.

  (* ===================================================================== *)
  (* Core preservation lemmas -- the separation-logic content of wakeup.    *)
  (* ===================================================================== *)

  (* the two parked states both demand the context obligation, so the obligation
     [proc_ctx] carries UNCHANGED across the SLEEPING -> RUNNABLE transition
     that wakeup performs. *)
  Lemma needs_ctx_SLEEPING : needs_ctx SLEEPING = true.
  Proof. rewrite /needs_ctx orb_true_r. done. Qed.

  Lemma needs_ctx_RUNNABLE : needs_ctx RUNNABLE = true.
  Proof.
    rewrite /needs_ctx. rewrite (bool_decide_eq_true_2 (RUNNABLE = RUNNABLE)); done.
  Qed.

  (* reassemble [proc_lock_res] from its parts -- what wakeup does at every
     [release]: whatever the (possibly updated) state, if it now demands a
     context we supply the (carried) [proc_ctx]. *)
  Lemma proc_lock_res_intro (γ : gname) (pa : mword 64) (st : mword 32) (ch : mword 64) :
    p_state pa ↦₄ st -∗
    p_chan pa ↦₈ ch -∗
    (if needs_ctx st then proc_ctx γ pa else emp) -∗
    proc_lock_res γ pa.
  Proof. iIntros "Hs Hc Hctx". iExists st, ch. iFrame. Qed.

  Lemma proc_lock_res_elim (γ : gname) (pa : mword 64) :
    proc_lock_res γ pa -∗
    ∃ (st : mword 32) (ch : mword 64),
      p_state pa ↦₄ st ∗ p_chan pa ↦₈ ch ∗
      (if needs_ctx st then proc_ctx γ pa else emp).
  Proof. iIntros "H". iExact "H". Qed.

  (* the wakeup transition: a proc found SLEEPING (hence carrying [proc_ctx]),
     with its state cell flipped to RUNNABLE, still satisfies [proc_lock_res].
     The saved context (with the lock token in its resumer predicate) survives
     the state change untouched. *)
  Lemma proc_lock_res_wakeup (γ : gname) (pa : mword 64) (ch : mword 64) :
    p_state pa ↦₄ RUNNABLE -∗
    p_chan pa ↦₈ ch -∗
    proc_ctx γ pa -∗
    proc_lock_res γ pa.
  Proof.
    iIntros "Hs Hc Hctx". iExists RUNNABLE, ch. iFrame "Hs Hc".
    destruct (needs_ctx RUNNABLE) eqn:Hn.
    - iExact "Hctx".
    - rewrite needs_ctx_RUNNABLE in Hn. discriminate.
  Qed.

  (* ===================================================================== *)
  (* Resource layout for the wakeup() WP.                                   *)
  (*                                                                        *)
  (* [spF] is wakeup's frame pointer -- the sp value AFTER the [c.addi16sp  *)
  (* sp,-64] prologue.  acquire/release are called with sp = spF and place  *)
  (* their spill/push_off/mycpu scratch BELOW spF at the exact offsets       *)
  (* recomputed here (so these cells UNIFY with the acquire/release specs).  *)
  (* ===================================================================== *)

  Definition off32m6 : mword 64 := sign_extend' 64 (sign_extend' 12 (mword_of_int 32 : mword 6)).
  Definition off48m6 : mword 64 := sign_extend' 64 (sign_extend' 12 (mword_of_int 48 : mword 6)).
  Definition wk_spd   (spF : mword 64) : mword 64 := add_vec spF (off32m6).           (* spF - 32 *)
  Definition wk_pospd (spF : mword 64) : mword 64 := add_vec (wk_spd spF) (off32m6).   (* spF - 64 *)
  Definition wk_pospm (spF : mword 64) : mword 64 := add_vec (wk_pospd spF) (off48m6). (* spF - 80 *)
  Definition wk_cell (base : mword 64) (n : Z) : mword 64 :=
    add_vec base (zero_extend' 64 (concat_vec (mword_of_int n : mword 6) ('b"000"))).

  (* the 9 acquire/release scratch cells (shared: spd+{1,2,3}, pospd+{1,2,3};
     release-only: pospd+0; both: pospm+{0,1}), contents irrelevant. *)
  Definition wk_scratch (spF : mword 64) : iProp Σ :=
    (∃ u1 u2 u3 u4 u5 u6 u7 u8 u9 : bv 64,
       wk_cell (wk_spd spF) 3 ↦₈ u1 ∗ wk_cell (wk_spd spF) 2 ↦₈ u2 ∗
       wk_cell (wk_spd spF) 1 ↦₈ u3 ∗
       wk_cell (wk_pospd spF) 3 ↦₈ u4 ∗ wk_cell (wk_pospd spF) 2 ↦₈ u5 ∗
       wk_cell (wk_pospd spF) 1 ↦₈ u6 ∗ wk_cell (wk_pospd spF) 0 ↦₈ u7 ∗
       wk_cell (wk_pospm spF) 1 ↦₈ u8 ∗ wk_cell (wk_pospm spF) 0 ↦₈ u9)%I.

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
     the (fixed) entry noff, restored by each acquire/release pair. *)
  Definition wk_res (γs : list gname) (spF a0f : mword 64) (noffv : mword 32) : iProp Σ :=
    (wk_scratch spF ∗
     wk_noff_addr a0f ↦₄ noffv ∗
     wk_intena_addr a0f ↦₄ (zeros' 32) ∗
     wk_lockcells γs)%I.

  (* register-map shape at the loop test [pc = wakeup+0x38] with counter [i]:
     the loop/callee-saved registers hold their fixed values (a0/a5 are scratch,
     hence existential in the map). *)
  Definition wk_regs (M : gmap regidx (mword 64))
      (spF sp0 rra rtp : mword 64) (chan : mword 64) (i : nat) : Prop :=
    M !!! Regidx (mword_of_int 1)  = rra /\
    M !!! Regidx (mword_of_int 2)  = spF /\
    M !!! Regidx (mword_of_int 8)  = sp0 /\
    M !!! Regidx (mword_of_int 9)  = proc_addr i /\
    M !!! Regidx (mword_of_int 4)  = rtp /\
    M !!! Regidx (mword_of_int 18) = proc_addr 64 /\
    M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64) /\
    M !!! Regidx (mword_of_int 20) = chan /\
    M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
    (forall r : regidx, r ∈ dom M).

End ProcInv.

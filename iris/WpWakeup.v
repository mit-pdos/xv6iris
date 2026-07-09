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
Require Import WpSmodeGpr WpMemsetS WpPushOff WpPushOffMem VcGen VcGenS.
Require Import WpAcquireTop WpAcquireLock WpAcquireMem WpRelease WpMycpu WpPushOffTop.
Require Import WpSwtchVc.
Require Import RiscvExec RiscvExtras RiscvTryStep WpDecode WpFetch WpLeafCommon WpRvcBridge WpKallocDecode WpAuipc.
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

  (* p++ : &proc[k] + sizeof(proc) = &proc[k+1].  The addi's 12-bit immediate
     [360] sign-extends to the same 64-bit constant, and mword addition agrees
     with Z addition mod 2^64 (via [avi_mword]). *)
  Lemma proc_addr_succ (k : nat) :
    add_vec (proc_addr k) (sign_extend' 64 (mword_of_int proc_size : mword 12)) = proc_addr (S k).
  Proof.
    unfold proc_addr. rewrite po_addv_assoc.
    assert (Hsx : sign_extend' 64 (mword_of_int proc_size : mword 12) = (mword_of_int proc_size : mword 64))
      by (apply bv_eq; vm_compute; reflexivity).
    rewrite Hsx. f_equal.
    change (add_vec (mword_of_int (proc_size * Z.of_nat k) : mword 64) (mword_of_int proc_size))
      with (add_vec_int (mword_of_int (proc_size * Z.of_nat k) : mword 64) proc_size).
    rewrite avi_mword. f_equal. rewrite Nat2Z.inj_succ. ring.
  Qed.

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
    menvcfg0 = MENVCFG_S ->
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
    iIntros (HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hrd)
      "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlbinv Hpc Hfile Hinstr Hcont".
    unshelve iApply (wp_gpr_write_s_config root_ppn E Φ pc rd
              (zero_extend' 5 ('b"00")) (zero_extend' 5 ('b"00"))
              (ITYPE (sign_extend' 12 imm, zreg, Regidx rd, ADDI))
              (add_vec zero_reg (sign_extend' 64 (sign_extend' 12 imm)))
              m mstatus0 mie_v mdv0 menvcfg0
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval Hrd
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
          r ∈ [mword_of_int 2; mword_of_int 4; mword_of_int 8; mword_of_int 9;
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
    M !!! Regidx (mword_of_int 9)  = proc_addr i /\
    M !!! Regidx (mword_of_int 4)  = rtp /\
    M !!! Regidx (mword_of_int 18) = proc_addr 64 /\
    M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64) /\
    M !!! Regidx (mword_of_int 20) = chan /\
    M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
    (forall r : regidx, r ∈ dom M).

  (* ===================================================================== *)
  (* Prologue: wakeup+0x00 .. the [c.j] to the loop test at wakeup+0x38.     *)
  (* Saves ra/s0/s1..s5, sets up s1=&proc[0], s2=&proc[64], s3=SLEEPING,     *)
  (* s4=chan, s5=RUNNABLE, then jumps to the loop test.                      *)
  (* ===================================================================== *)
  (* peel nested [<[k:=v]>_ !!! j] map lookups down to the base map. *)
  Local Ltac wk_peel :=
    repeat first
      [ rewrite lookup_total_insert
      | (rewrite lookup_total_insert_ne; [ idtac | vm_compute; discriminate ]) ].

  Lemma wp_wakeup_prologue (m : gmap regidx (mword 64))
      (f7 f6 f5 f4 f3 f2 f1 : bv 64) :
    ↑minstretN ⊆ E ->
    (forall r : regidx, r ∈ dom m) ->
    let spF := add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
    kernel_text -∗
    pc_is (mword_of_int KernelSyms.wakeup) -∗ gpr_file m -∗
    wk_fcell spF 7 ↦₈ f7 -∗ wk_fcell spF 6 ↦₈ f6 -∗ wk_fcell spF 5 ↦₈ f5 -∗
    wk_fcell spF 4 ↦₈ f4 -∗ wk_fcell spF 3 ↦₈ f3 -∗ wk_fcell spF 2 ↦₈ f2 -∗
    wk_fcell spF 1 ↦₈ f1 -∗
    ( ∀ M : gmap regidx (mword 64),
        ⌜ wk_regs M spF (m !!! Regidx (mword_of_int 2 : mword 5))
            (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 4 : mword 5))
            (m !!! Regidx (mword_of_int 10 : mword 5)) 0 ⌝ -∗
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
        kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗ gpr_file M -∗
        wk_frame spF (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
          (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
          (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
          (m !!! Regidx (mword_of_int 21 : mword 5)) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN Hdom spF.
    iIntros "Hsm Hgc Htlb #Htext Hpc Hfile Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1 Hcont".
    iPoseProof (wki_00 with "Htext") as "Hi00".
    iPoseProof (wki_02 with "Htext") as "Hi02".
    (* ---- f44: c.addi16sp sp,-64 (bundled) ---- *)
    iApply (wp_caddi16sp_gpr_s root_ppn γc E Phi (mword_of_int KernelSyms.wakeup)
              (mword_of_int 60 : mword 6) m 1 HN
              with "Hsm Htlb Hpc Hfile Hi00 [-]").
    iIntros "Hsm Htlb Hpc Hfile".
    (* the new sp value is exactly [spF]. *)
    set (M1 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (m !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))))]> m).
    assert (HM1sp : M1 !!! Regidx csp_rs1 = spF).
    { subst M1 spF. by rewrite lookup_total_insert. }
    (* unbundle config into raw cells for the store leaves *)
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hms0 & Hmie0 & Hmenv0)".
    iDestruct "Hms0" as (mstatus0) "(Hms & Hsieg & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie0" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenv0" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %HLPE & %HFIOM & %Hmenvval)".
    (* pc: wakeup+0x02 *)
    assert (Hpp02 : add_vec_int (mword_of_int KernelSyms.wakeup : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x02)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp02) in "Hpc".
    (* ---- f46: c.sdsp ra,56(sp) ---- *)
    iEval (rewrite /wk_fcell -HM1sp) in "Hc7".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x02))
              (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) M1 f7
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi02 Hc7 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc7".
    (* the [c.sdsp] leaf's [m !!! Regidx rs2] store-value: expose it. *)
    assert (Hrav : M1 !!! Regidx (mword_of_int 1 : mword 5) = m !!! Regidx (mword_of_int 1 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite Hrav) in "Hc7".
    (* ---- f48: c.sdsp s0,48(sp) ---- *)
    iPoseProof (wki_04 with "Htext") as "Hi04".
    assert (Hpp04 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x02) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x04)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp04) in "Hpc".
    assert (Hs0v : M1 !!! Regidx (mword_of_int 8 : mword 5) = m !!! Regidx (mword_of_int 8 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc6".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x04))
              (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) M1 f6
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi04 Hc6 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc6".
    iEval (rewrite Hs0v) in "Hc6".
    (* ---- f4a: c.sdsp s1,40(sp) ---- *)
    iPoseProof (wki_06 with "Htext") as "Hi06".
    assert (Hpp06 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x04) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x06)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp06) in "Hpc".
    assert (Hs1v : M1 !!! Regidx (mword_of_int 9 : mword 5) = m !!! Regidx (mword_of_int 9 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc5".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x06))
              (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5) M1 f5
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi06 Hc5 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc5".
    iEval (rewrite Hs1v) in "Hc5".
    (* ---- f4c: c.sdsp s2,32(sp) ---- *)
    iPoseProof (wki_08 with "Htext") as "Hi08".
    assert (Hpp08 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x06) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x08)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp08) in "Hpc".
    assert (Hs2v : M1 !!! Regidx (mword_of_int 18 : mword 5) = m !!! Regidx (mword_of_int 18 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc4".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x08))
              (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5) M1 f4
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi08 Hc4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc4".
    iEval (rewrite Hs2v) in "Hc4".
    (* ---- f4e: c.sdsp s3,24(sp) ---- *)
    iPoseProof (wki_0a with "Htext") as "Hi0a".
    assert (Hpp0a : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x08) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x0a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0a) in "Hpc".
    assert (Hs3v : M1 !!! Regidx (mword_of_int 19 : mword 5) = m !!! Regidx (mword_of_int 19 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc3".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x0a))
              (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5) M1 f3
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi0a Hc3 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc3".
    iEval (rewrite Hs3v) in "Hc3".
    (* ---- f50: c.sdsp s4,16(sp) ---- *)
    iPoseProof (wki_0c with "Htext") as "Hi0c".
    assert (Hpp0c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x0a) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x0c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0c) in "Hpc".
    assert (Hs4v : M1 !!! Regidx (mword_of_int 20 : mword 5) = m !!! Regidx (mword_of_int 20 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc2".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x0c))
              (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5) M1 f2
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi0c Hc2 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc2".
    iEval (rewrite Hs4v) in "Hc2".
    (* ---- f52: c.sdsp s5,8(sp) ---- *)
    iPoseProof (wki_0e with "Htext") as "Hi0e".
    assert (Hpp0e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x0c) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x0e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp0e) in "Hpc".
    assert (Hs5v : M1 !!! Regidx (mword_of_int 21 : mword 5) = m !!! Regidx (mword_of_int 21 : mword 5)).
    { subst M1. rewrite lookup_total_insert_ne; [reflexivity | vm_compute; discriminate]. }
    iEval (rewrite /wk_fcell -HM1sp) in "Hc1".
    iApply (wp_csdsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x0e))
              (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5) M1 f1
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi0e Hc1 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc1".
    iEval (rewrite Hs5v) in "Hc1".
    (* ---- f54: c.addi4spn s0,sp,64  (s0 := spF + 64 = sp0) ---- *)
    iPoseProof (wki_10 with "Htext") as "Hi10".
    assert (Hpp10 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x0e) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x10)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp10) in "Hpc".
    iApply (wp_caddi4spn_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x10))
              (Cregidx (mword_of_int 0)) (mword_of_int 16 : mword 8) (mword_of_int 8 : mword 5) M1
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi10 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f56: c.mv s4,a0  (s4 := chan) ---- *)
    iPoseProof (wki_12 with "Htext") as "Hi12".
    assert (Hpp12 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x10) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x12)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp12) in "Hpc".
    iApply (wp_cmv_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x12))
              (mword_of_int 20 : mword 5) (mword_of_int 10 : mword 5) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi12 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f58: auipc s1,0x11 ---- *)
    iPoseProof (wki_14 with "Htext") as "Hi14".
    assert (Hpp14 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x12) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x14)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp14) in "Hpc".
    iApply (wp_auipc_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x14))
              (mword_of_int 9 : mword 5) (mword_of_int 0x11 : mword 20) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi14 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f5c: addi s1,s1,-2016  (s1 := proc_base) ---- *)
    iPoseProof (wki_18 with "Htext") as "Hi18".
    assert (Hpp18 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x14) : mword 64) 4
                    = mword_of_int (KernelSyms.wakeup + 0x18)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp18) in "Hpc".
    iApply (wp_addi4_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x18))
              (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 2080 : mword 12) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi18 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f60: c.li s3,2 ---- *)
    iPoseProof (wki_1c with "Htext") as "Hi1c".
    assert (Hpp1c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x18) : mword 64) 4
                    = mword_of_int (KernelSyms.wakeup + 0x1c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1c) in "Hpc".
    iApply (wp_cli_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x1c))
              (mword_of_int 19 : mword 5) (mword_of_int 2 : mword 6) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi1c [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f62: c.li s5,3 ---- *)
    iPoseProof (wki_1e with "Htext") as "Hi1e".
    assert (Hpp1e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x1c) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x1e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp1e) in "Hpc".
    iApply (wp_cli_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x1e))
              (mword_of_int 21 : mword 5) (mword_of_int 3 : mword 6) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi1e [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f64: auipc s2,0x16 ---- *)
    iPoseProof (wki_20 with "Htext") as "Hi20".
    assert (Hpp20 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x1e) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x20)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp20) in "Hpc".
    iApply (wp_auipc_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x20))
              (mword_of_int 18 : mword 5) (mword_of_int 0x16 : mword 20) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi20 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f68: addi s2,s2,532  (s2 := proc_addr 64) ---- *)
    iPoseProof (wki_24 with "Htext") as "Hi24".
    assert (Hpp24 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x20) : mword 64) 4
                    = mword_of_int (KernelSyms.wakeup + 0x24)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp24) in "Hpc".
    iApply (wp_addi4_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x24))
              (mword_of_int 18 : mword 5) (mword_of_int 18 : mword 5) (mword_of_int 532 : mword 12) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(vm_compute; discriminate)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi24 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    (* ---- f6c: c.j -> wakeup+0x38 (loop test) ---- *)
    iPoseProof (wki_28 with "Htext") as "Hi28".
    assert (Hpp28 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x24) : mword 64) 4
                    = mword_of_int (KernelSyms.wakeup + 0x28)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp28) in "Hpc".
    assert (Hjtgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x28) : mword 64)
                      (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0"))))
                    = mword_of_int (KernelSyms.wakeup + 0x38)) by (apply bv_eq; vm_compute; reflexivity).
    iApply (wp_cj_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x28))
              (sign_extend' 21 (concat_vec (mword_of_int 8 : mword 11) ('b"0"))) _
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN HSIE HMPRV HSXL Hmm HPBMTE Hmenvval ltac:(rewrite Hjtgt; vm_compute; reflexivity)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi28 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    iEval (rewrite Hjtgt) in "Hpc".
    (* rebuild the S-mode config bundle *)
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm HLPE HFIOM Hmenvval
                 with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
    (* key value identities for the final register map *)
    assert (Hprocbase : add_vec (add_vec (mword_of_int (KernelSyms.wakeup + 0x14) : mword 64)
                          (auipc_off (mword_of_int 0x11 : mword 20)))
                          (sign_extend' 64 (mword_of_int 2080 : mword 12)) = proc_base)
      by (unfold proc_base; apply bv_eq; vm_compute; reflexivity).
    assert (Hproc64 : add_vec (add_vec (mword_of_int (KernelSyms.wakeup + 0x20) : mword 64)
                        (auipc_off (mword_of_int 0x16 : mword 20)))
                        (sign_extend' 64 (mword_of_int 532 : mword 12)) = proc_addr 64)
      by (unfold proc_addr, proc_base, proc_size; apply bv_eq; vm_compute; reflexivity).
    iApply ("Hcont" with "[%] Hsm Hgc Htlb Htext Hpc Hfile [Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1]").
    { (* wk_regs *)
      unfold wk_regs.
      repeat split.
      - (* ra *) wk_peel. reflexivity.
      - (* sp *) wk_peel. reflexivity.
      - (* s1 = proc_addr 0 *) wk_peel.
        rewrite Hprocbase. unfold proc_addr. apply bv_eq; vm_compute; reflexivity.
      - (* tp *) wk_peel. reflexivity.
      - (* s2 = proc_addr 64 *) wk_peel.
        rewrite Hproc64. reflexivity.
      - (* s3 = 2 *) wk_peel.
        apply bv_eq; vm_compute; reflexivity.
      - (* s4 = chan *) wk_peel. rewrite aq_addv_zero_l. reflexivity.
      - (* s5 = 3 *) wk_peel.
        apply bv_eq; vm_compute; reflexivity.
      - (* dom *) intro r. pose proof (Hdom r) as Hr.
        (* was [set_solver] -- ~128s here, as naive_solver rescans the whole
           (huge) proof context; the goal is just [r ∈ union-tower ∪ dom base]
           with [Hr : r ∈ dom base], so route right and close directly. *)
        rewrite !dom_insert_L. repeat apply elem_of_union_r. exact Hr. }
    { (* wk_frame *)
      unfold wk_frame.
      iEval (rewrite HM1sp) in "Hc7". iEval (rewrite HM1sp) in "Hc6".
      iEval (rewrite HM1sp) in "Hc5". iEval (rewrite HM1sp) in "Hc4".
      iEval (rewrite HM1sp) in "Hc3". iEval (rewrite HM1sp) in "Hc2".
      iEval (rewrite HM1sp) in "Hc1".
      iFrame "Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1". }
  Qed.

  (* ===================================================================== *)
  (* Epilogue: wakeup+0x58 (the [DONE] label) .. the [c.ret].               *)
  (* Restores ra/s0/s1..s5 from the frame, pops the 64-byte frame, and      *)
  (* returns to the (bit-0-cleared) saved return address.                   *)
  (* ===================================================================== *)
  Lemma wp_wakeup_epilogue (M : gmap regidx (mword 64))
      (spF : mword 64) (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64) :
    ↑minstretN ⊆ E ->
    M !!! Regidx csp_rs1 = spF ->
    (forall r : regidx, r ∈ dom M) ->
    let rettgt := update_vec_dec (add_vec vra (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
    eq_vec (access_vec_dec rettgt 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗ gpr_file M -∗
    wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
    ( ∀ Mf : gmap regidx (mword 64),
        ⌜ Mf !!! Regidx (mword_of_int 1)  = vra
        /\ Mf !!! Regidx (mword_of_int 8)  = vs0
        /\ Mf !!! Regidx (mword_of_int 9)  = vs1
        /\ Mf !!! Regidx (mword_of_int 18) = vs2
        /\ Mf !!! Regidx (mword_of_int 19) = vs3
        /\ Mf !!! Regidx (mword_of_int 20) = vs4
        /\ Mf !!! Regidx (mword_of_int 21) = vs5
        /\ Mf !!! Regidx csp_rs1 =
             add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))
        /\ (forall r : regidx, r ∈ dom Mf) ⌝ -∗
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
        kernel_text -∗ pc_is rettgt -∗ gpr_file Mf -∗
        wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN HspF Hdom rettgt Halign.
    iIntros "Hsm Hgc Htlb #Htext Hpc Hfile Hframe Hcont".
    iDestruct "Hframe" as "(Hc7 & Hc6 & Hc5 & Hc4 & Hc3 & Hc2 & Hc1)".
    (* unbundle config into raw cells for the c.ldsp / c.ret leaves *)
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hms0 & Hmie0 & Hmenv0)".
    iDestruct "Hms0" as (mstatus0) "(Hms & Hsieg & %HSIE & %HMPRV & %HSXL & %HMXR & %Hleg)".
    iDestruct "Hmie0" as (mie_v mdv0) "(Hmie & Hmdl & %Hmm)".
    iDestruct "Hmenv0" as (menvcfg0) "(Hmenv & %HPBMTE & %Hpmm & %HLPE & %HFIOM & %Hmenvval)".
    (* ---- f9c: c.ldsp ra,56(sp) ---- *)
    iPoseProof (wki_58 with "Htext") as "Hi58".
    iEval (rewrite /wk_fcell -HspF) in "Hc7".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x58))
              (mword_of_int 7 : mword 6) (mword_of_int 1 : mword 5) M vra
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi58 Hc7 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc7".
    set (M1 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg vra]> M).
    assert (Hsp1 : M1 !!! Regidx csp_rs1 = spF)
      by (rewrite /M1 lookup_total_insert_ne; [exact HspF | vm_compute; discriminate]).
    iEval (rewrite HspF) in "Hc7".
    assert (Hpp5a : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x58) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x5a)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5a) in "Hpc".
    (* ---- f9e: c.ldsp s0,48(sp) ---- *)
    iPoseProof (wki_5a with "Htext") as "Hi5a".
    iEval (rewrite /wk_fcell -Hsp1) in "Hc6".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x5a))
              (mword_of_int 6 : mword 6) (mword_of_int 8 : mword 5) M1 vs0
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi5a Hc6 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc6".
    set (M2 := <[Regidx (mword_of_int 8 : mword 5) := regval_into_reg vs0]> M1).
    assert (Hsp2 : M2 !!! Regidx csp_rs1 = spF)
      by (rewrite /M2 lookup_total_insert_ne; [exact Hsp1 | vm_compute; discriminate]).
    iEval (rewrite Hsp1) in "Hc6".
    assert (Hpp5c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x5a) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x5c)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5c) in "Hpc".
    (* ---- fa0: c.ldsp s1,40(sp) ---- *)
    iPoseProof (wki_5c with "Htext") as "Hi5c".
    iEval (rewrite /wk_fcell -Hsp2) in "Hc5".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x5c))
              (mword_of_int 5 : mword 6) (mword_of_int 9 : mword 5) M2 vs1
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi5c Hc5 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc5".
    set (M3 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg vs1]> M2).
    assert (Hsp3 : M3 !!! Regidx csp_rs1 = spF)
      by (rewrite /M3 lookup_total_insert_ne; [exact Hsp2 | vm_compute; discriminate]).
    iEval (rewrite Hsp2) in "Hc5".
    assert (Hpp5e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x5c) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x5e)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp5e) in "Hpc".
    (* ---- fa2: c.ldsp s2,32(sp) ---- *)
    iPoseProof (wki_5e with "Htext") as "Hi5e".
    iEval (rewrite /wk_fcell -Hsp3) in "Hc4".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x5e))
              (mword_of_int 4 : mword 6) (mword_of_int 18 : mword 5) M3 vs2
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi5e Hc4 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc4".
    set (M4 := <[Regidx (mword_of_int 18 : mword 5) := regval_into_reg vs2]> M3).
    assert (Hsp4 : M4 !!! Regidx csp_rs1 = spF)
      by (rewrite /M4 lookup_total_insert_ne; [exact Hsp3 | vm_compute; discriminate]).
    iEval (rewrite Hsp3) in "Hc4".
    assert (Hpp60 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x5e) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x60)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp60) in "Hpc".
    (* ---- fa4: c.ldsp s3,24(sp) ---- *)
    iPoseProof (wki_60 with "Htext") as "Hi60".
    iEval (rewrite /wk_fcell -Hsp4) in "Hc3".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x60))
              (mword_of_int 3 : mword 6) (mword_of_int 19 : mword 5) M4 vs3
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi60 Hc3 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc3".
    set (M5 := <[Regidx (mword_of_int 19 : mword 5) := regval_into_reg vs3]> M4).
    assert (Hsp5 : M5 !!! Regidx csp_rs1 = spF)
      by (rewrite /M5 lookup_total_insert_ne; [exact Hsp4 | vm_compute; discriminate]).
    iEval (rewrite Hsp4) in "Hc3".
    assert (Hpp62 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x60) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x62)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp62) in "Hpc".
    (* ---- fa6: c.ldsp s4,16(sp) ---- *)
    iPoseProof (wki_62 with "Htext") as "Hi62".
    iEval (rewrite /wk_fcell -Hsp5) in "Hc2".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x62))
              (mword_of_int 2 : mword 6) (mword_of_int 20 : mword 5) M5 vs4
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi62 Hc2 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc2".
    set (M6 := <[Regidx (mword_of_int 20 : mword 5) := regval_into_reg vs4]> M5).
    assert (Hsp6 : M6 !!! Regidx csp_rs1 = spF)
      by (rewrite /M6 lookup_total_insert_ne; [exact Hsp5 | vm_compute; discriminate]).
    iEval (rewrite Hsp5) in "Hc2".
    assert (Hpp64 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x62) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x64)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp64) in "Hpc".
    (* ---- fa8: c.ldsp s5,8(sp) ---- *)
    iPoseProof (wki_64 with "Htext") as "Hi64".
    iEval (rewrite /wk_fcell -Hsp6) in "Hc1".
    iApply (wp_cldsp_gpr_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x64))
              (mword_of_int 1 : mword 6) (mword_of_int 21 : mword 5) M6 vs5
              mstatus0 mie_v mdv0 menvcfg0 (dq:=DfracOwn 1)
              HN ltac:(vm_compute; discriminate) HSIE HMPRV HSXL Hmm HMXR Hpmm HPBMTE Hmenvval
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi64 Hc1 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hc1".
    set (M7 := <[Regidx (mword_of_int 21 : mword 5) := regval_into_reg vs5]> M6).
    assert (Hsp7 : M7 !!! Regidx csp_rs1 = spF)
      by (rewrite /M7 lookup_total_insert_ne; [exact Hsp6 | vm_compute; discriminate]).
    iEval (rewrite Hsp6) in "Hc1".
    assert (Hpp66 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x64) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x66)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp66) in "Hpc".
    (* ---- faa: c.addi16sp sp,+64 (bundled) ---- *)
    iPoseProof (wki_66 with "Htext") as "Hi66".
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus0 mie_v mdv0 menvcfg0
                 HSIE HMPRV HSXL HMXR Hleg Hmm HPBMTE Hpmm HLPE HFIOM Hmenvval
                 with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
    iApply (wp_caddi16sp_gpr_s root_ppn γc E Phi (mword_of_int (KernelSyms.wakeup + 0x66))
              (mword_of_int 4 : mword 6) M7 1 HN
              with "Hsm Htlb Hpc Hfile Hi66 [-]").
    iIntros "Hsm Htlb Hpc Hfile".
    set (M8 := <[Regidx csp_rs1 := regval_into_reg
        (add_vec (M7 !!! Regidx csp_rs1) (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6))))]> M7).
    assert (Hpp68 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x66) : mword 64) 2
                    = mword_of_int (KernelSyms.wakeup + 0x68)) by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hpp68) in "Hpc".
    (* ---- fac: c.ret (unbundle again for the raw c.ret leaf) ---- *)
    iPoseProof (wki_68 with "Htext") as "Hi68".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(_ & _ & Hhs & Hpriv & Hms0 & Hmie0 & Hmenv0)".
    iDestruct "Hms0" as (mstatus1) "(Hms & Hsieg & %HSIE1 & %HMPRV1 & %HSXL1 & %HMXR1 & %Hleg1)".
    iDestruct "Hmie0" as (mie_v1 mdv1) "(Hmie & Hmdl & %Hmm1)".
    iDestruct "Hmenv0" as (menvcfg1) "(Hmenv & %HPBMTE1 & %Hpmm1 & %HLPE1 & %HFIOM1 & %Hmenvval1)".
    (* the c.ret target computed by the leaf from [M8 !!! ra] is [rettgt]. *)
    assert (HM8ra : M8 !!! Regidx (mword_of_int 1 : mword 5) = vra).
    { rewrite /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1. wk_peel. reflexivity. }
    iApply (wp_cret_s_zca root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x68))
              (mword_of_int 1 : mword 5) M8
              mstatus1 mie_v1 mdv1 menvcfg1 (dq:=DfracOwn 1)
              HN HSIE1 HMPRV1 HSXL1 Hmm1 HPBMTE1 Hmenvval1
              ltac:(vm_compute; discriminate) HLPE1
              ltac:(rewrite HM8ra; exact Halign)
              with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi68 [-]").
    iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
    iEval (rewrite HM8ra) in "Hpc".
    (* rebuild config for the continuation *)
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mstatus1 mie_v1 mdv1 menvcfg1
                 HSIE1 HMPRV1 HSXL1 HMXR1 Hleg1 Hmm1 HPBMTE1 Hpmm1 HLPE1 HFIOM1 Hmenvval1
                 with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
    iApply ("Hcont" $! M8 with "[%] Hsm Hgc Htlb Htext Hpc Hfile [Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1]").
    { (* register facts about the final map M8 *)
      rewrite /M8 /M7 /M6 /M5 /M4 /M3 /M2 /M1.
      repeat split.
      - (* ra *) wk_peel. reflexivity.
      - (* s0 *) wk_peel. reflexivity.
      - (* s1 *) wk_peel. reflexivity.
      - (* s2 *) wk_peel. reflexivity.
      - (* s3 *) wk_peel. reflexivity.
      - (* s4 *) wk_peel. reflexivity.
      - (* s5 *) wk_peel. reflexivity.
      - (* sp *) wk_peel. rewrite HspF. reflexivity.
      - (* dom *) intro r. pose proof (Hdom r) as Hr.
        (* context-free replacement for [set_solver] -- see wp_wakeup_prologue. *)
        rewrite !dom_insert_L. repeat apply elem_of_union_r. exact Hr. }
    { (* wk_frame reassembly *)
      unfold wk_frame. iFrame "Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1". }
  Qed.

  (* register-map shape at the loop header [pc = wakeup+0x38] with counter [k].
     Same as [wk_regs] but WITHOUT the [ra] constraint: [ra] is dead at the
     header (immediately clobbered by the [jal myproc]). *)
  Definition wk_loop_regs (M : gmap regidx (mword 64)) (spF rtp chan : mword 64) (k : nat) : Prop :=
    M !!! Regidx (mword_of_int 9)  = proc_addr k /\
    M !!! Regidx (mword_of_int 2)  = spF /\
    M !!! Regidx (mword_of_int 4)  = rtp /\
    M !!! Regidx (mword_of_int 18) = proc_addr NPROC /\
    M !!! Regidx (mword_of_int 19) = (mword_of_int 2 : mword 64) /\
    M !!! Regidx (mword_of_int 20) = chan /\
    M !!! Regidx (mword_of_int 21) = (mword_of_int 3 : mword 64) /\
    (forall r : regidx, r ∈ dom M).

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
  Lemma wk_csp2 : Regidx csp_rs1 = Regidx (mword_of_int 2 : mword 5).
  Proof. vm_compute. reflexivity. Qed.

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
  Lemma wp_wakeup_loop
      (γs : list gname) (spF a0f rtp chan : mword 64) (noffv : mword 32)
      (vra vs0 vs1 vs2 vs3 vs4 vs5 : mword 64) :
    ↑minstretN ⊆ E -> ↑lockN ⊆ E ->
    length γs = NPROC ->
    mycpu_ret rtp = a0f ->
    eq_vec (zero_reg : mword 64) (mycpu_ret rtp) = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 (wk_noff_acq noffv)) = false ->
    wk_noff_rel (wk_noff_acq noffv) = noffv ->
    procs_inv γs -∗
    (* the loop's exit continuation: control at the epilogue entry [wakeup+0x58]. *)
    ( ∀ Mexit : gmap regidx (mword 64),
        ⌜ Mexit !!! Regidx csp_rs1 = spF /\ (forall r : regidx, r ∈ dom Mexit) ⌝ -∗
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
        kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗ gpr_file Mexit -∗
        wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    ∀ (k : nat) (M : gmap regidx (mword 64)),
      ⌜(k < NPROC)%nat⌝ -∗ ⌜wk_loop_regs M spF rtp chan k⌝ -∗
      smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
      kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗ gpr_file M -∗
      wk_res γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
      WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN HNl Hlen Ha0f Hmycpu_nz Hnf_pos Hnf_rt.
    iIntros "#Hpinv Hqexit".
    (* the loop is BOUNDED (at most NPROC iterations), so we do ordinary Coq
       induction on a [fuel] bounding the remaining iterations [NPROC - k] -- no
       Löb/▷ needed, so the packaged S-mode leaves (which hide the step's later)
       compose cleanly. *)
    iAssert (∀ (fuel k : nat) (M : gmap regidx (mword 64)),
               ⌜(NPROC - k <= fuel)%nat⌝ -∗ ⌜(k < NPROC)%nat⌝ -∗ ⌜wk_loop_regs M spF rtp chan k⌝ -∗
               ( ∀ Mexit : gmap regidx (mword 64),
                   ⌜ Mexit !!! Regidx csp_rs1 = spF /\ (forall r : regidx, r ∈ dom Mexit) ⌝ -∗
                   smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
                   kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x58)) -∗ gpr_file Mexit -∗
                   wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
                   WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
               smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
               kernel_text -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x38)) -∗ gpr_file M -∗
               wk_res γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
               WP (Loop : expr riscv_lang) @ E {{ Phi }})%I with "[]" as "Hloop".
    { iIntros (fuel). iInduction fuel as [|fuel IHf] "IHf".
      { (* fuel = 0 : [NPROC - k <= 0] with [k < NPROC] is absurd *)
        iIntros (k M) "%Hfuel %Hk %Hregs Hqexit Hsm Hgc Htlb Htext Hpc Hfile Hres Hframe".
        exfalso. lia. }
    iIntros (k M) "%Hfuel %Hk %Hregs Hqexit Hsm Hgc Htlb #Htext Hpc Hfile Hres Hframe".
    destruct Hregs as (Hs1 & Hsp & Htp & Hs2 & Hs3 & Hs4 & Hs5 & Hdom).
    (* ---- shared tail [pc = wakeup+0x30]: p++ (0x30 addi s1,s1,360), then the
       termination test (0x34 beq s1,s2): exit to the epilogue when p reaches
       &proc[NPROC], else recurse (Löb) into the next iteration. Captures the
       exit continuation [Hqexit] once; reached from both the skip-self path
       (0x3c taken) and the release-return path (0x2c). ---- *)
    iAssert (∀ Mt : gmap regidx (mword 64),
               ⌜ wk_loop_regs Mt spF rtp chan k ⌝ -∗
               smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
               pc_is (mword_of_int (KernelSyms.wakeup + 0x30)) -∗ gpr_file Mt -∗
               wk_res γs spF a0f noffv -∗ wk_frame spF vra vs0 vs1 vs2 vs3 vs4 vs5 -∗
               WP (Loop : expr riscv_lang) @ E {{ Phi }})%I
      with "[Hqexit]" as "Htail".
    { iIntros (Mt) "%Hmt Hsm Hgc Htlb Hpc Hfile Hres Hframe".
      destruct Hmt as (Ht1 & Htsp & Http & Ht18 & Ht19 & Ht20 & Ht21 & Htdom).
      iPoseProof (wki_30 with "Htext") as "Hi30".
      iPoseProof (wki_34 with "Htext") as "Hi34".
      iDestruct (smode_config_unbundle with "Hsm") as
        "(#Hhw & #Hinv & Hhs & Hpriv & HmsA & HmieA & HmenvA)".
      iDestruct "HmsA" as (mstA) "(Hms & Hsieg & %HSIEA & %HMPRVA & %HSXLA & %HMXRA & %HlegA)".
      iDestruct "HmieA" as (mievA mdvA) "(Hmie & Hmdl & %HmmA)".
      iDestruct "HmenvA" as (menvA) "(Hmenv & %HPBMTEA & %HpmmA & %HLPEA & %HFIOMA & %HmenvvalA)".
      (* 0x30 addi s1,s1,360 : s1 := &proc[k+1] *)
      iApply (wp_gpr_write_s_config_base root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x30))
                (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5)
                (ITYPE (mword_of_int 360 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI))
                (proc_addr (S k)) Mt mstA mievA mdvA menvA (dq:=DfracOwn 1)
                HN HSIEA HMPRVA HSXLA HmmA HPBMTEA HmenvvalA ltac:(vm_compute; discriminate)
                ltac:(intros s_pc Hnpc Hva Hvb;
                      assert (Hval : gpr_addi_val (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12) s_pc = proc_addr (S k));
                      [ unfold gpr_addi_val; rewrite Hva; rewrite Ht1; apply (proc_addr_succ k) | ];
                      rewrite (exec_execute_ITYPE_ADDI_gpr (mword_of_int 9 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 360 : mword 12) s_pc);
                      rewrite Hval;
                      replace (Z.eqb (uint (mword_of_int 9 : mword 5)) 0) with false by (vm_compute; reflexivity);
                      reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi30 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
      set (Mt30 := <[Regidx (mword_of_int 9 : mword 5) := regval_into_reg (proc_addr (S k))]> Mt).
      assert (Hpp34 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x30) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x34))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp34) in "Hpc".
      assert (HMt30_9 : Mt30 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr (S k))
        by (rewrite /Mt30; apply lookup_total_insert).
      assert (HMt30_18 : Mt30 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
      { rewrite /Mt30 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Ht18. }
      (* 0x34 beq s1,s2 : exit iff &proc[k+1] = &proc[NPROC].  Manual case split
         (so the full spatial context is available in BOTH branches). *)
      destruct (eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                       (Mt30 !!! Regidx (mword_of_int 18 : mword 5))) eqn:Hcmp.
      + (* TAKEN: p reached &proc[NPROC]; exit to epilogue at wakeup+0x58 *)
        iApply (wp_beq_taken_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x34))
                  (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                  Mt30 mstA mievA mdvA menvA (dq:=DfracOwn 1)
                  HN HSIEA HMPRVA HSXLA HmmA HPBMTEA HmenvvalA
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp ltac:(vm_compute; reflexivity)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi34").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
        assert (Htgt58 : add_vec (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64)
                           (sign_extend' 64 (mword_of_int 36 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x58))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Htgt58) in "Hpc".
        iDestruct (smode_config_rebuild γc (DfracOwn 1) mstA mievA mdvA menvA
                     HSIEA HMPRVA HSXLA HMXRA HlegA HmmA HPBMTEA HpmmA HLPEA HFIOMA HmenvvalA
                     with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
        iApply ("Hqexit" $! Mt30 with "[] Hsm Hgc Htlb Htext Hpc Hfile Hframe").
        iPureIntro. split.
        * rewrite /Mt30 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Htsp.
        * intro r. rewrite /Mt30 dom_insert_L. apply elem_of_union_r. apply Htdom.
      + (* FALL: p < &proc[NPROC]; recurse into iteration k+1 *)
        iApply (wp_beq_fall_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x34))
                  (mword_of_int 36 : mword 13) (mword_of_int 18 : mword 5) (mword_of_int 9 : mword 5)
                  Mt30 mstA mievA mdvA menvA (dq:=DfracOwn 1)
                  HN HSIEA HMPRVA HSXLA HmmA HPBMTEA HmenvvalA
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi34").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
        assert (HkS : (S k < NPROC)%nat).
        { destruct (Nat.lt_ge_cases (S k) NPROC) as [Hlt | Hge]; [exact Hlt|].
          assert (HeqN : S k = NPROC) by lia.
          exfalso.
          assert (Hbad : eq_vec (Mt30 !!! Regidx (mword_of_int 9 : mword 5))
                           (Mt30 !!! Regidx (mword_of_int 18 : mword 5)) = true).
          { rewrite HMt30_9 HMt30_18 HeqN. apply wk_eq_vec_refl. }
          rewrite Hcmp in Hbad. discriminate. }
        assert (Hpp38 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x34) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x38))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp38) in "Hpc".
        iDestruct (smode_config_rebuild γc (DfracOwn 1) mstA mievA mdvA menvA
                     HSIEA HMPRVA HSXLA HMXRA HlegA HmmA HPBMTEA HpmmA HLPEA HFIOMA HmenvvalA
                     with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
        iApply ("IHf" $! (S k) Mt30 with "[%] [%] [%] Hqexit Hsm Hgc Htlb Htext Hpc Hfile Hres Hframe").
        * lia.
        * exact HkS.
        * unfold wk_loop_regs.
          split; [exact HMt30_9|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Htsp | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Http | vm_compute; discriminate]|].
          split; [exact HMt30_18|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht19 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht20 | vm_compute; discriminate]|].
          split; [rewrite /Mt30 lookup_total_insert_ne; [exact Ht21 | vm_compute; discriminate]|].
          intro r. rewrite /Mt30 dom_insert_L. apply elem_of_union_r. apply Htdom. }
    iPoseProof (wki_38 with "Htext") as "Hi38".
    (* extract the persistent hw_config/minstret_inv for the (2-aligned-target)
       zca jal leaves used by the myproc/acquire/release calls. *)
    iDestruct (smode_config_unbundle with "Hsm") as
      "(#Hhw & #Hinv & Hhs & Hpriv & Hms0 & Hmie0 & Hmenv0)".
    iDestruct "Hms0" as (mst0) "(Hms & Hsieg & %HSIE0 & %HMPRV0 & %HSXL0 & %HMXR0 & %Hleg0)".
    iDestruct "Hmie0" as (miev0 mdv0) "(Hmie & Hmdl & %Hmm0)".
    iDestruct "Hmenv0" as (menv0) "(Hmenv & %HPBMTE0 & %Hpmm0 & %HLPE0 & %HFIOM0 & %Hmenvval0)".
    iDestruct (smode_config_rebuild γc (DfracOwn 1) mst0 miev0 mdv0 menv0
                 HSIE0 HMPRV0 HSXL0 HMXR0 Hleg0 Hmm0 HPBMTE0 Hpmm0 HLPE0 HFIOM0 Hmenvval0
                 with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
    (* ---- 0x38: jal ra, myproc (base JAL, 2-aligned target) ---- *)
    iApply (wp_jal_gpr_s_zca root_ppn γc E Phi (mword_of_int (KernelSyms.wakeup + 0x38))
              (mword_of_int 1 : mword 5) (mword_of_int 2095482 : mword 21) M 1%Qp
              HN ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
              with "Hhw Hsm Htlb Hpc Hfile Hi38 [-]").
    iIntros "Hsm Htlb Hpc Hfile".
    set (Mj := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg
        (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)]> M).
    assert (Hjtgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64)
                      (sign_extend' 64 (mword_of_int 2095482 : mword 21)) = mword_of_int KernelSyms.myproc)
      by (apply bv_eq; vm_compute; reflexivity).
    iEval (rewrite Hjtgt) in "Hpc".
    assert (HMjra : Mj !!! Regidx (mword_of_int 1 : mword 5)
                    = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x38) : mword 64) 4)
      by (rewrite /Mj; apply lookup_total_insert).
    (* ---- myproc(): returns a0 = proc_addr j (j<NPROC), preserves callee-saved ---- *)
    iApply (wp_myproc root_ppn E Phi γc bsie Mj HN
              ltac:(rewrite HMjra; vm_compute; reflexivity)
              with "Hsm Hgc Htlb Htext Hpc Hfile [-]").
    iIntros (j mret) "%Hj %Hreta0 %Hpres Hsm Hgc Htlb Hpc Hfile".
    (* pc is now wakeup+0x3c (myproc's bit-0-cleared return target) *)
    assert (Hret3c : update_vec_dec (add_vec (Mj !!! Regidx (mword_of_int 1 : mword 5))
                       (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                     = mword_of_int (KernelSyms.wakeup + 0x3c)).
    { rewrite HMjra. apply bv_eq; vm_compute; reflexivity. }
    iEval (rewrite Hret3c) in "Hpc".
    (* s1 is preserved by myproc: mret!!!s1 = proc_addr k *)
    assert (Hmrets1 : mret !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
    { rewrite (Hpres (mword_of_int 9 : mword 5) ltac:(compute_done)).
      rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs1. }
    (* ---- 0x3c: beq a0,s1 (raw leaf): skip-self test ---- *)
    iPoseProof (wki_3c with "Htext") as "Hi3c".
    iDestruct (smode_config_unbundle with "Hsm") as
      "(_ & _ & Hhs & Hpriv & Hms1 & Hmie1 & Hmenv1)".
    iDestruct "Hms1" as (mst1) "(Hms & Hsieg & %HSIE1 & %HMPRV1 & %HSXL1 & %HMXR1 & %Hleg1)".
    iDestruct "Hmie1" as (miev1 mdv1) "(Hmie & Hmdl & %Hmm1)".
    iDestruct "Hmenv1" as (menv1) "(Hmenv & %HPBMTE1 & %Hpmm1 & %HLPE1 & %HFIOM1 & %Hmenvval1)".
    destruct (eq_vec (mret !!! Regidx (mword_of_int 10 : mword 5))
                     (mret !!! Regidx (mword_of_int 9 : mword 5))) eqn:Hcmp3.
    - (* TAKEN: a0 = s1 (current proc is myproc): skip to 0x30 (p++) *)
      iApply (wp_beq_taken_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x3c))
                (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                mret mst1 miev1 mdv1 menv1 (dq:=DfracOwn 1)
                HN HSIE1 HMPRV1 HSXL1 Hmm1 HPBMTE1 Hmenvval1
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp3 ltac:(vm_compute; reflexivity)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi3c").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
      assert (Htgt30 : add_vec (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64)
                         (sign_extend' 64 (mword_of_int 8180 : mword 13)) = mword_of_int (KernelSyms.wakeup + 0x30))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Htgt30) in "Hpc".
      iDestruct (gpr_file_dom with "Hfile") as "[%Hdommret Hfile]".
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mst1 miev1 mdv1 menv1
                   HSIE1 HMPRV1 HSXL1 HMXR1 Hleg1 Hmm1 HPBMTE1 Hpmm1 HLPE1 HFIOM1 Hmenvval1
                   with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
      iApply ("Htail" $! mret with "[] Hsm Hgc Htlb Hpc Hfile Hres Hframe").
      iPureIntro. unfold wk_loop_regs.
      split; [exact Hmrets1|].
      split; [rewrite (Hpres (mword_of_int 2 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Hsp | vm_compute; discriminate]|].
      split; [rewrite (Hpres (mword_of_int 4 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Htp | vm_compute; discriminate]|].
      split; [rewrite (Hpres (mword_of_int 18 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Hs2 | vm_compute; discriminate]|].
      split; [rewrite (Hpres (mword_of_int 19 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Hs3 | vm_compute; discriminate]|].
      split; [rewrite (Hpres (mword_of_int 20 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Hs4 | vm_compute; discriminate]|].
      split; [rewrite (Hpres (mword_of_int 21 : mword 5) ltac:(compute_done));
              rewrite /Mj lookup_total_insert_ne; [exact Hs5 | vm_compute; discriminate]|].
      exact Hdommret.
    - (* FALL: a0 <> s1: acquire proc[k], check state/chan, maybe wake, release *)
      iApply (wp_beq_fall_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x3c))
                (mword_of_int 8180 : mword 13) (mword_of_int 9 : mword 5) (mword_of_int 10 : mword 5)
                mret mst1 miev1 mdv1 menv1 (dq:=DfracOwn 1)
                HN HSIE1 HMPRV1 HSXL1 Hmm1 HPBMTE1 Hmenvval1
                ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                Hcmp3
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi3c").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
      assert (Hpp40 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x3c) : mword 64) 4 = mword_of_int (KernelSyms.wakeup + 0x40))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp40) in "Hpc".
      (* the per-proc lock for proc[k], and its protected resource. *)
      destruct (lookup_lt_is_Some_2 γs k ltac:(rewrite Hlen; exact Hk)) as [γk Hγk].
      iDestruct (procs_inv_lookup γs k γk Hγk with "Hpinv") as "#Hlockk".
      (* open [wk_res]: scratch cells, noff/intena words, per-proc lock->cpu words. *)
      iDestruct "Hres" as "(Hscr & Hnoffc & Hintc & Hlockcells)".
      iDestruct (big_sepL_lookup_acc _ _ _ _ Hγk with "Hlockcells") as "[Hcpuk Hlockback]".
      iDestruct "Hscr" as (u1 u2 u3 u4 u5 u6 u7 u8 u9)
        "(Hu1 & Hu2 & Hu3 & Hu4 & Hu5 & Hu6 & Hu7 & Hu8 & Hu9)".
      (* sp/tp preserved through myproc (needed for acquire's frame + a0f). *)
      assert (Hmret2 : mret !!! Regidx (mword_of_int 2 : mword 5) = spF).
      { rewrite (Hpres (mword_of_int 2 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hsp. }
      assert (Hmret4 : mret !!! Regidx (mword_of_int 4 : mword 5) = rtp).
      { rewrite (Hpres (mword_of_int 4 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Htp. }
      iPoseProof (wki_40 with "Htext") as "Hi40".
      (* 0x40 c.mv a0,s1 : a0 := &proc[k] *)
      iApply (wp_cmv_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x40))
                (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                mret mst1 miev1 mdv1 menv1 (dq:=DfracOwn 1)
                HN HSIE1 HMPRV1 HSXL1 Hmm1 HPBMTE1 Hmenvval1 ltac:(vm_compute; discriminate)
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi40 [-]").
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
      set (M40 := <[Regidx (mword_of_int 10 : mword 5) :=
                    regval_into_reg (add_vec zero_reg (mret !!! Regidx (mword_of_int 9 : mword 5)))]> mret).
      assert (Hpp42 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x40) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x42))
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpp42) in "Hpc".
      iPoseProof (wki_42 with "Htext") as "Hi42".
      (* 0x42 jal ra,acquire *)
      iDestruct (smode_config_rebuild γc (DfracOwn 1) mst1 miev1 mdv1 menv1
                   HSIE1 HMPRV1 HSXL1 HMXR1 Hleg1 Hmm1 HPBMTE1 Hpmm1 HLPE1 HFIOM1 Hmenvval1
                   with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
      iApply (wp_jal_gpr_s_zca root_ppn γc E Phi (mword_of_int (KernelSyms.wakeup + 0x42))
                (mword_of_int 1 : mword 5) (mword_of_int 2092148 : mword 21) M40 1%Qp
                HN ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                with "Hhw Hsm Htlb Hpc Hfile Hi42 [-]").
      iIntros "Hsm Htlb Hpc Hfile".
      set (M42 := <[Regidx (mword_of_int 1 : mword 5) :=
                    regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)]> M40).
      assert (Hjtgt_aq : add_vec (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64)
                          (sign_extend' 64 (mword_of_int 2092148 : mword 21)) = mword_of_int KernelSyms.acquire)
        by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hjtgt_aq) in "Hpc".
      assert (HM42ra : M42 !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x42) : mword 64) 4)
        by (rewrite /M42; apply lookup_total_insert).
      assert (HM42a0 : M42 !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert. rewrite add_vec_zero_l. exact Hmrets1. }
      assert (HM42csp : M42 !!! Regidx csp_rs1 = spF).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret2. }
      assert (HM42tp : M42 !!! Regidx (mword_of_int 4 : mword 5) = rtp).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret4. }
      (* acquire(&proc[k]->lock): CSL acquire returns [locked γk ∗ proc_lock_res]. *)
      iApply (wp_acquire_lock root_ppn E Phi γk (proc_lock_res γk (proc_addr k)) M42
                u1 u2 u3 u4 u5 u6 u8 u9 (zero_reg : mword 64)
                noffv (zeros' 32) a0f γc bsie
                HN HNl
                ltac:(rewrite HM42tp; exact Ha0f)
                ltac:(rewrite HM42tp; exact Hmycpu_nz)
                ltac:(rewrite HM42ra; vm_compute; reflexivity)
                with "Hsm Hgc Htlb Htext Hpc Hfile
                      [Hu1] [Hu2] [Hu3] [Hu4] [Hu5] [Hu6] [Hu8] [Hu9] [Hnoffc] [Hintc] [Hlockk] [Hcpuk] [-]").
      { iEval (rewrite HM42csp). iExact "Hu1". }
      { iEval (rewrite HM42csp). iExact "Hu2". }
      { iEval (rewrite HM42csp). iExact "Hu3". }
      { iEval (rewrite HM42csp). iExact "Hu4". }
      { iEval (rewrite HM42csp). iExact "Hu5". }
      { iEval (rewrite HM42csp). iExact "Hu6". }
      { iEval (rewrite HM42csp). iExact "Hu8". }
      { iEval (rewrite HM42csp). iExact "Hu9". }
      { iExact "Hnoffc". }
      { iExact "Hintc". }
      { iEval (rewrite HM42a0). iExact "Hlockk". }
      { iEval (rewrite HM42a0). iExact "Hcpuk". }
      iIntros "Hsm Hgc Htlb Hpc Htok HR Hgpr Har24 Har16 Har8 Hjunk Hnoff2 Hint2 Hcpu2".
      (* acquire's push_off saved the intena as [if <old noff=0> then 0 else 0];
         collapse the (trivially constant) conditional so it matches [wk_res]'s
         bare [zeros' 32] on the release round-trip. *)
      assert (Hif_int : forall b : bool, (if b then (zeros' 32 : mword 32) else zeros' 32) = zeros' 32)
        by (intro b; destruct b; reflexivity).
      iEval (rewrite (Hif_int (eq_vec (sign_extend' 64 noffv) zero_reg))) in "Hint2".
      (* acquire returned: [locked γk] held, R = proc_lock_res, pc = wakeup+0x46. *)
      assert (Hpc46 : update_vec_dec (add_vec (M42 !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                      = mword_of_int (KernelSyms.wakeup + 0x46)).
      { rewrite HM42ra. apply bv_eq; vm_compute; reflexivity. }
      iEval (rewrite Hpc46) in "Hpc".
      iDestruct "Hgpr" as (Macq) "[Hfile %Hpins]".
      iDestruct (proc_lock_res_elim with "HR") as (st ch) "(Hpst & Hpch & Hctx)".
      (* register-preservation through acquire. *)
      destruct Hpins as (Hf1 & Hf8 & Hf9 & Hfcsp & Hf10 & Hf4 & Hf18 & Hf19 & Hf20 & Hf21).
      assert (HM42s1 : M42 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmrets1. }
      assert (Hmret18 : mret !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
      { rewrite (Hpres (mword_of_int 18 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs2. }
      assert (Hmret19 : mret !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64)).
      { rewrite (Hpres (mword_of_int 19 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs3. }
      assert (Hmret20 : mret !!! Regidx (mword_of_int 20 : mword 5) = chan).
      { rewrite (Hpres (mword_of_int 20 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs4. }
      assert (Hmret21 : mret !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64)).
      { rewrite (Hpres (mword_of_int 21 : mword 5) ltac:(compute_done)).
        rewrite /Mj lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hs5. }
      assert (HM42s2 : M42 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret18. }
      assert (HM42s3 : M42 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64)).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret19. }
      assert (HM42s4 : M42 !!! Regidx (mword_of_int 20 : mword 5) = chan).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret20. }
      assert (HM42s5 : M42 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64)).
      { rewrite /M42 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite /M40 lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hmret21. }
      assert (HMacq9 : Macq !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k) by (rewrite Hf9; exact HM42s1).
      assert (HMacq2 : Macq !!! Regidx csp_rs1 = spF) by (rewrite Hfcsp; exact HM42csp).
      assert (HMacq4 : Macq !!! Regidx (mword_of_int 4 : mword 5) = rtp) by (rewrite Hf4; exact HM42tp).
      assert (HMacq18 : Macq !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC) by (rewrite Hf18; exact HM42s2).
      assert (HMacq19 : Macq !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64)) by (rewrite Hf19; exact HM42s3).
      assert (HMacq20 : Macq !!! Regidx (mword_of_int 20 : mword 5) = chan) by (rewrite Hf20; exact HM42s4).
      assert (HMacq21 : Macq !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64)) by (rewrite Hf21; exact HM42s5).
      (* clean the acquire-returned frame cells into [wk_cell spF] / [proc_addr k] form. *)
      iEval (rewrite HM42csp) in "Har24".
      iEval (rewrite HM42csp) in "Har16".
      iEval (rewrite HM42csp) in "Har8".
      iEval (rewrite HM42a0) in "Hcpu2".
      iEval (rewrite HM42tp) in "Hcpu2".
      iDestruct "Hjunk" as (vp24 vp16 vp8 vfra vfs0) "(Hp24 & Hp16 & Hp8 & Hfra & Hfs0)".
      iEval (rewrite HM42csp) in "Hp24".
      iEval (rewrite HM42csp) in "Hp16".
      iEval (rewrite HM42csp) in "Hp8".
      iEval (rewrite HM42csp) in "Hfra".
      iEval (rewrite HM42csp) in "Hfs0".
      (* unbundle the config for the post-acquire straight-line leaves. *)
      iDestruct (smode_config_unbundle with "Hsm") as
        "(_ & _ & Hhs & Hpriv & Hms2 & Hmie2 & Hmenv2)".
      iDestruct "Hms2" as (mst2) "(Hms & Hsieg & %HSIE2 & %HMPRV2 & %HSXL2 & %HMXR2 & %Hleg2)".
      iDestruct "Hmie2" as (miev2 mdv2) "(Hmie & Hmdl & %Hmm2)".
      iDestruct "Hmenv2" as (menv2) "(Hmenv & %HPBMTE2 & %Hpmm2 & %HLPE2 & %HFIOM2 & %Hmenvval2)".
      (* =============================================================== *)
      (* shared release tail [Hrel], reached from all 3 exits (state !=      *)
      (* SLEEPING, chan mismatch, or after waking).  It runs 0x2a mv a0,s1;  *)
      (* 0x2c jal release; then returns to the p++ tail [Htail] at 0x30.     *)
      (* =============================================================== *)
      iAssert (∀ (Mr : gmap regidx (mword 64)),
                 ⌜ Mr !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k /\
                   Mr !!! Regidx (mword_of_int 2 : mword 5) = spF /\
                   Mr !!! Regidx (mword_of_int 4 : mword 5) = rtp /\
                   Mr !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC /\
                   Mr !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64) /\
                   Mr !!! Regidx (mword_of_int 20 : mword 5) = chan /\
                   Mr !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64) /\
                   (forall r : regidx, r ∈ dom Mr) ⌝ -∗
                 hart_state ↦ᵣ{ DfracOwn 1 } HART_ACTIVE tt -∗
                 cur_privilege ↦ᵣ{ DfracOwn 1 } Supervisor -∗
                 mstatus ↦ᵣ{ DfracOwn 1 } mst2 -∗ mie ↦ᵣ{ DfracOwn 1 } miev2 -∗
                 mideleg ↦ᵣ{ DfracOwn 1 } mdv2 -∗ menvcfg ↦ᵣ{ DfracOwn 1 } menv2 -∗
                 tlb_inv root_ppn -∗ pc_is (mword_of_int (KernelSyms.wakeup + 0x2a)) -∗
                 gpr_file Mr -∗ locked γk -∗ proc_lock_res γk (proc_addr k) -∗
                 WP (Loop : expr riscv_lang) @ E {{ Phi }})%I
        with "[Hgc Hsieg Har24 Har16 Har8 Hp24 Hp16 Hp8 Hu7 Hfra Hfs0 Hnoff2 Hint2 Hcpu2 Hlockback Hframe Htail]"
        as "Hrel".
      { iIntros (Mr) "%Hmr Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Htok HR".
        destruct Hmr as (Hr9 & Hr2 & Hr4 & Hr18 & Hr19 & Hr20 & Hr21 & Hrdom).
        iPoseProof (wki_2a with "Htext") as "Hi2a".
        iPoseProof (wki_2c with "Htext") as "Hi2c".
        (* 0x2a c.mv a0,s1 : a0 := &proc[k] *)
        iApply (wp_cmv_gpr_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x2a))
                  (mword_of_int 10 : mword 5) (mword_of_int 9 : mword 5)
                  Mr mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                  HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2 ltac:(vm_compute; discriminate)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi2a [-]").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
        set (Mr2a := <[Regidx (mword_of_int 10 : mword 5) :=
                       regval_into_reg (add_vec zero_reg (Mr !!! Regidx (mword_of_int 9 : mword 5)))]> Mr).
        assert (Hpp2c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2a) : mword 64) 2 = mword_of_int (KernelSyms.wakeup + 0x2c))
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpp2c) in "Hpc".
        iDestruct (smode_config_rebuild γc (DfracOwn 1) mst2 miev2 mdv2 menv2
                     HSIE2 HMPRV2 HSXL2 HMXR2 Hleg2 Hmm2 HPBMTE2 Hpmm2 HLPE2 HFIOM2 Hmenvval2
                     with "Hhw Hinv Hhs Hpriv Hms Hsieg Hmie Hmdl Hmenv") as "Hsm".
        (* 0x2c jal ra,release *)
        iApply (wp_jal_gpr_s_zca root_ppn γc E Phi (mword_of_int (KernelSyms.wakeup + 0x2c))
                  (mword_of_int 1 : mword 5) (mword_of_int 2092306 : mword 21) Mr2a 1%Qp
                  HN ltac:(vm_compute; discriminate) ltac:(vm_compute; reflexivity)
                  with "Hhw Hsm Htlb Hpc Hfile Hi2c [-]").
        iIntros "Hsm Htlb Hpc Hfile".
        set (Mr2c := <[Regidx (mword_of_int 1 : mword 5) :=
                       regval_into_reg (add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)]> Mr2a).
        assert (Hjtgt_rl : add_vec (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64)
                            (sign_extend' 64 (mword_of_int 2092306 : mword 21)) = mword_of_int KernelSyms.release)
          by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hjtgt_rl) in "Hpc".
        assert (HMr2c_ra : Mr2c !!! Regidx (mword_of_int 1 : mword 5) = add_vec_int (mword_of_int (KernelSyms.wakeup + 0x2c) : mword 64) 4)
          by (rewrite /Mr2c; apply lookup_total_insert).
        assert (HMr2c_a0 : Mr2c !!! Regidx (mword_of_int 10 : mword 5) = proc_addr k).
        { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Mr2a lookup_total_insert. rewrite add_vec_zero_l. exact Hr9. }
        assert (HMr2c_csp : Mr2c !!! Regidx csp_rs1 = spF).
        { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr2. }
        assert (HMr2c_tp : Mr2c !!! Regidx (mword_of_int 4 : mword 5) = rtp).
        { rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
          rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr4. }
        (* release(&proc[k]->lock) : returns the lock+resource into the invariant. *)
        iApply (wp_release root_ppn E Phi γk γc bsie (proc_addr k) (proc_lock_res γk (proc_addr k)) Mr2c
                  (mycpu_ret rtp) (wk_noff_acq noffv) (zeros' 32)
                  _ _ _ _ _ _ _ _ _ (dqi:=DfracOwn 1)
                  HN HNl
                  ltac:(rewrite HMr2c_a0; apply wk_add_vec_0)
                  ltac:(rewrite HMr2c_tp; apply wk_eq_vec_refl)
                  Hnf_pos
                  ltac:(vm_compute; reflexivity)
                  ltac:(rewrite HMr2c_ra; vm_compute; reflexivity)
                  with "Hsm Hgc Htlb Htext Hpc Hfile Hlockk Htok HR [Hcpu2] [Hnoff2] [Hint2] [Har24] [Har16] [Har8] [Hp24] [Hp16] [Hp8] [Hu7] [Hfra] [Hfs0] [-]").
        { iEval (rewrite HMr2c_a0). iExact "Hcpu2". }
        { iEval (rewrite HMr2c_tp). iEval (rewrite Ha0f). iExact "Hnoff2". }
        { iEval (rewrite HMr2c_tp). iEval (rewrite Ha0f). iExact "Hint2". }
        { iEval (rewrite HMr2c_csp). iExact "Har24". }
        { iEval (rewrite HMr2c_csp). iExact "Har16". }
        { iEval (rewrite HMr2c_csp). iExact "Har8". }
        { iEval (rewrite HMr2c_csp). iExact "Hp24". }
        { iEval (rewrite HMr2c_csp). iExact "Hp16". }
        { iEval (rewrite HMr2c_csp). iExact "Hp8". }
        { iEval (rewrite HMr2c_csp). iExact "Hu7". }
        { iEval (rewrite HMr2c_csp). iExact "Hfra". }
        { iEval (rewrite HMr2c_csp). iExact "Hfs0". }
        iIntros "Hsm Hgc Htlb Hpc Hgpr Hcpu3 Hnoff3 Hint3 Hjunk3".
        (* pc = wakeup+0x30 (release's return target). *)
        assert (Hpc30 : update_vec_dec (add_vec (Mr2c !!! Regidx (mword_of_int 1 : mword 5)) (sign_extend' 64 (zeros' 12))) 0 ('b"0")
                        = mword_of_int (KernelSyms.wakeup + 0x30)).
        { rewrite HMr2c_ra. apply bv_eq; vm_compute; reflexivity. }
        iEval (rewrite Hpc30) in "Hpc".
        iDestruct "Hgpr" as (mr) "[Hfile %Hpinsr]".
        destruct Hpinsr as (Hr'1 & Hr'8 & Hr'9 & Hr'csp & Hr'4 & Hr'18 & Hr'19 & Hr'20 & Hr'21).
        iDestruct (gpr_file_dom with "Hfile") as "[%Hdommr Hfile]".
        (* reassemble [wk_res] for the next iteration: scratch (release junk),
           noff (restored to noffv via the round-trip), intena (0), lock words. *)
        iDestruct "Hjunk3" as (w1 w2 w3 w4 w5 w6 w7 w8 w9) "(Hw1 & Hw2 & Hw3 & Hw4 & Hw5 & Hw6 & Hw7 & Hw8 & Hw9)".
        iEval (rewrite HMr2c_csp) in "Hw1".
        iEval (rewrite HMr2c_csp) in "Hw2".
        iEval (rewrite HMr2c_csp) in "Hw3".
        iEval (rewrite HMr2c_csp) in "Hw4".
        iEval (rewrite HMr2c_csp) in "Hw5".
        iEval (rewrite HMr2c_csp) in "Hw6".
        iEval (rewrite HMr2c_csp) in "Hw7".
        iEval (rewrite HMr2c_csp) in "Hw8".
        iEval (rewrite HMr2c_csp) in "Hw9".
        iEval (rewrite HMr2c_a0) in "Hcpu3".
        iEval (rewrite HMr2c_tp) in "Hnoff3". iEval (rewrite Ha0f) in "Hnoff3".
        iEval (rewrite HMr2c_tp) in "Hint3". iEval (rewrite Ha0f) in "Hint3".
        iApply ("Htail" $! mr with "[%] Hsm Hgc Htlb Hpc Hfile [Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9 Hnoff3 Hint3 Hcpu3 Hlockback] Hframe").
        - (* wk_loop_regs mr spF rtp chan k *)
          unfold wk_loop_regs.
          split.
          { rewrite Hr'9. rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr9. }
          split; [exact (eq_trans Hr'csp HMr2c_csp)|].
          split; [rewrite Hr'4; exact HMr2c_tp|].
          split.
          { rewrite Hr'18. rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr18. }
          split.
          { rewrite Hr'19. rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr19. }
          split.
          { rewrite Hr'20. rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr20. }
          split.
          { rewrite Hr'21. rewrite /Mr2c lookup_total_insert_ne; [| vm_compute; discriminate].
            rewrite /Mr2a lookup_total_insert_ne; [| vm_compute; discriminate]. exact Hr21. }
          exact Hdommr.
        - (* wk_res: scratch ∗ noff ∗ intena ∗ lockcells *)
          rewrite /wk_res. iSplitL "Hw1 Hw2 Hw3 Hw4 Hw5 Hw6 Hw7 Hw8 Hw9".
          { rewrite /wk_scratch. iExists w1, w2, w3, w4, w5, w6, w7, w8, w9. iFrame. }
          iSplitL "Hnoff3".
          { (* rewrite ONLY the goal (via iEval): a bare Coq [rewrite] would also
               hit [noffv] inside Hnoff3 in the proof-mode context, desyncing them.
               [iExact] then closes by conversion (wk_noff_rel unfolds to release's
               storeval_noff). *)
            iEval (rewrite <- Hnf_rt). iExact "Hnoff3". }
          iSplitL "Hint3". { iExact "Hint3". }
          iApply "Hlockback". iExact "Hcpu3". }
      (* ================================================================= *)
      (* 2c: state/chan test + wake, dispatching to [Hrel] at 3 release      *)
      (* exits.                                                              *)
      (*   0x46 c.lw  a5,24(s1)   a5 := sext(p->state)                       *)
      (*   0x48 bne   a5,s3, rel  if state != SLEEPING -> release            *)
      (*   0x4c c.ld  a5,32(s1)   a5 := p->chan                              *)
      (*   0x4e bne   a5,s4, rel  if chan != arg -> release                  *)
      (*   0x52 sw    s5,24(s1)   p->state := RUNNABLE   (wake)              *)
      (*   0x56 c.j   rel                                                     *)
      (* ================================================================= *)
      iDestruct (gpr_file_dom with "Hfile") as "[%Hdomacq Hfile]".
      (* ---- 0x46 c.lw a5,24(s1) : a5 := sext(state) ---- *)
      iPoseProof (wki_46 with "Htext") as "Hi46".
      iEval (rewrite wk_cr1; rewrite wk_cr7) in "Hi46".
      assert (Hea46 : add_vec (Macq !!! Regidx (mword_of_int 9 : mword 5))
                        (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
                      = p_state (proc_addr k)).
      { rewrite HMacq9. rewrite /p_state /state_off.
        replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00"))))
           with (mword_of_int 24 : mword 64) by (apply bv_eq; vm_compute; reflexivity).
        reflexivity. }
      iApply (wp_clw_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x46))
                (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5)
                (zero_extend' 12 (concat_vec (mword_of_int 6 : mword 5) ('b"00")))
                Macq st mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                HN ltac:(vm_compute; discriminate) HSIE2 HMPRV2 HSXL2 Hmm2 HMXR2 Hpmm2 HPBMTE2 Hmenvval2
                with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi46 [Hpst] [-]").
      { iEval (rewrite Hea46). iExact "Hpst". }
      iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hpst".
      iEval (rewrite Hea46) in "Hpst".
      set (M48 := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg (sign_extend' 64 st)]> Macq).
      assert (Hpc48 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x46) : mword 64) 2
                      = mword_of_int (KernelSyms.wakeup + 0x48)) by (apply bv_eq; vm_compute; reflexivity).
      iEval (rewrite Hpc48) in "Hpc".
      (* register facts for M48 (only x15 was written). *)
      assert (HM48a5 : M48 !!! Regidx (mword_of_int 15 : mword 5) = sign_extend' 64 st)
        by (rewrite /M48 lookup_total_insert; reflexivity).
      assert (HM48_9 : M48 !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq9 | vm_compute; discriminate]).
      assert (HM48_2 : M48 !!! Regidx (mword_of_int 2 : mword 5) = spF).
      { rewrite /M48 lookup_total_insert_ne; [| vm_compute; discriminate].
        rewrite <- wk_csp2. exact HMacq2. }
      assert (HM48_4 : M48 !!! Regidx (mword_of_int 4 : mword 5) = rtp)
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq4 | vm_compute; discriminate]).
      assert (HM48_18 : M48 !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq18 | vm_compute; discriminate]).
      assert (HM48_19 : M48 !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq19 | vm_compute; discriminate]).
      assert (HM48_20 : M48 !!! Regidx (mword_of_int 20 : mword 5) = chan)
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq20 | vm_compute; discriminate]).
      assert (HM48_21 : M48 !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
        by (rewrite /M48 lookup_total_insert_ne; [exact HMacq21 | vm_compute; discriminate]).
      assert (HdomM48 : forall r : regidx, r ∈ dom M48).
      { intro r. rewrite /M48 dom_insert_L. apply elem_of_union_r. apply Hdomacq. }
      (* ---- 0x48 bne a5,s3 : if state != SLEEPING -> release ---- *)
      iPoseProof (wki_48 with "Htext") as "Hi48".
      destruct (neq_vec (M48 !!! Regidx (mword_of_int 15 : mword 5))
                        (M48 !!! Regidx (mword_of_int 19 : mword 5))) eqn:Hcmp48.
      + (* TAKEN: state != SLEEPING -> reassemble proc_lock_res, release *)
        iApply (wp_bne_taken_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x48))
                  (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                  M48 mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                  HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp48 ltac:(vm_compute; reflexivity)
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi48 [-]").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
        assert (H48tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64)
                          (sign_extend' 64 (mword_of_int 8162 : mword 13))
                        = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite H48tgt) in "Hpc".
        iDestruct (proc_lock_res_intro γk (proc_addr k) st ch with "Hpst Hpch Hctx") as "HR".
        iApply ("Hrel" $! M48 with "[%] Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Htok HR").
        repeat split; [exact HM48_9 | exact HM48_2 | exact HM48_4 | exact HM48_18
                      | exact HM48_19 | exact HM48_20 | exact HM48_21 | exact HdomM48].
      + (* FALL: state == SLEEPING -> load chan ---- *)
        iApply (wp_bne_fall_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x48))
                  (mword_of_int 8162 : mword 13) (mword_of_int 19 : mword 5) (mword_of_int 15 : mword 5)
                  M48 mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                  HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2
                  ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                  Hcmp48
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi48 [-]").
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
        (* state == SLEEPING. *)
        assert (Heq2 : sign_extend' 64 st = (mword_of_int 2 : mword 64)).
        { rewrite HM48a5 HM48_19 in Hcmp48. unfold neq_vec in Hcmp48.
          rewrite negb_false_iff in Hcmp48. apply eq_vec_true_iff in Hcmp48. exact Hcmp48. }
        pose proof (wk_sext_sleeping st Heq2) as Hst_sl.
        assert (Hpc4c : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x48) : mword 64) 4
                        = mword_of_int (KernelSyms.wakeup + 0x4c)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc4c) in "Hpc".
        (* ---- 0x4c c.ld a5,32(s1) : a5 := p->chan ---- *)
        iPoseProof (wki_4c with "Htext") as "Hi4c".
        iEval (rewrite wk_cr1; rewrite wk_cr7) in "Hi4c".
        assert (Hea4c : add_vec (M48 !!! Regidx (mword_of_int 9 : mword 5))
                          (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) = p_chan (proc_addr k)).
        { rewrite HM48_9. rewrite /p_chan /chan_off.
          replace (sign_extend' 64 (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))) with (mword_of_int 32 : mword 64)
            by (apply bv_eq; vm_compute; reflexivity).
          reflexivity. }
        iApply (wp_cld_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x4c))
                  (mword_of_int 15 : mword 5) (mword_of_int 9 : mword 5) (zero_extend' 12 (concat_vec (mword_of_int 4 : mword 5) ('b"000")))
                  M48 ch mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                  HN ltac:(vm_compute; discriminate) HSIE2 HMPRV2 HSXL2 Hmm2 HMXR2 Hpmm2 HPBMTE2 Hmenvval2
                  with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi4c [Hpch] [-]").
        { iEval (rewrite Hea4c). iExact "Hpch". }
        iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hpch".
        iEval (rewrite Hea4c) in "Hpch".
        set (M4e := <[Regidx (mword_of_int 15 : mword 5) := regval_into_reg ch]> M48).
        assert (Hpc4e : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4c) : mword 64) 2
                        = mword_of_int (KernelSyms.wakeup + 0x4e)) by (apply bv_eq; vm_compute; reflexivity).
        iEval (rewrite Hpc4e) in "Hpc".
        assert (HM4e_a5 : M4e !!! Regidx (mword_of_int 15 : mword 5) = ch)
          by (rewrite /M4e lookup_total_insert; reflexivity).
        assert (HM4e_9 : M4e !!! Regidx (mword_of_int 9 : mword 5) = proc_addr k)
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_9 | vm_compute; discriminate]).
        assert (HM4e_2 : M4e !!! Regidx (mword_of_int 2 : mword 5) = spF)
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_2 | vm_compute; discriminate]).
        assert (HM4e_4 : M4e !!! Regidx (mword_of_int 4 : mword 5) = rtp)
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_4 | vm_compute; discriminate]).
        assert (HM4e_18 : M4e !!! Regidx (mword_of_int 18 : mword 5) = proc_addr NPROC)
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_18 | vm_compute; discriminate]).
        assert (HM4e_19 : M4e !!! Regidx (mword_of_int 19 : mword 5) = (mword_of_int 2 : mword 64))
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_19 | vm_compute; discriminate]).
        assert (HM4e_20 : M4e !!! Regidx (mword_of_int 20 : mword 5) = chan)
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_20 | vm_compute; discriminate]).
        assert (HM4e_21 : M4e !!! Regidx (mword_of_int 21 : mword 5) = (mword_of_int 3 : mword 64))
          by (rewrite /M4e lookup_total_insert_ne; [exact HM48_21 | vm_compute; discriminate]).
        assert (HdomM4e : forall r : regidx, r ∈ dom M4e).
        { intro r. rewrite /M4e dom_insert_L. apply elem_of_union_r. apply HdomM48. }
        (* ---- 0x4e bne a5,s4 : if chan != arg -> release ---- *)
        iPoseProof (wki_4e with "Htext") as "Hi4e".
        destruct (neq_vec (M4e !!! Regidx (mword_of_int 15 : mword 5))
                          (M4e !!! Regidx (mword_of_int 20 : mword 5))) eqn:Hcmp4e.
        * (* TAKEN: chan mismatch -> release *)
          iApply (wp_bne_taken_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x4e))
                    (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                    M4e mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                    HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp4e ltac:(vm_compute; reflexivity)
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi4e [-]").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
          assert (H4etgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64)
                            (sign_extend' 64 (mword_of_int 8156 : mword 13))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite H4etgt) in "Hpc".
          iDestruct (proc_lock_res_intro γk (proc_addr k) st ch with "Hpst Hpch Hctx") as "HR".
          iApply ("Hrel" $! M4e with "[%] Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Htok HR").
          repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_4 | exact HM4e_18
                        | exact HM4e_19 | exact HM4e_20 | exact HM4e_21 | exact HdomM4e].
        * (* FALL: chan matches -> wake (state := RUNNABLE) *)
          iApply (wp_bne_fall_s_config root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x4e))
                    (mword_of_int 8156 : mword 13) (mword_of_int 20 : mword 5) (mword_of_int 15 : mword 5)
                    M4e mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                    HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2
                    ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)
                    Hcmp4e
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi4e [-]").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
          assert (Hpc52 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x4e) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x52)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc52) in "Hpc".
          (* ---- 0x52 sw s5,24(s1) : p->state := RUNNABLE ---- *)
          iPoseProof (wki_52 with "Htext") as "Hi52".
          assert (Hea52 : add_vec (M4e !!! Regidx (mword_of_int 9 : mword 5))
                            (sign_extend' 64 (mword_of_int 24 : mword 12)) = p_state (proc_addr k)).
          { rewrite HM4e_9. rewrite /p_state /state_off.
            replace (sign_extend' 64 (mword_of_int 24 : mword 12)) with (mword_of_int 24 : mword 64)
              by (apply bv_eq; vm_compute; reflexivity).
            reflexivity. }
          iApply (wp_sw_s_ram root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x52))
                    (mword_of_int 21 : mword 5) (mword_of_int 9 : mword 5) (mword_of_int 24 : mword 12)
                    M4e st mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                    HN HSIE2 HMPRV2 HSXL2 Hmm2 HMXR2 Hpmm2 HPBMTE2 Hmenvval2
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi52 [Hpst] [-]").
          { iEval (rewrite Hea52). iExact "Hpst". }
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hpst".
          assert (Hstored : trunc32 (M4e !!! Regidx (mword_of_int 21 : mword 5)) = RUNNABLE).
          { rewrite HM4e_21. rewrite /RUNNABLE. apply bv_eq; vm_compute; reflexivity. }
          iEval (rewrite Hstored) in "Hpst". iEval (rewrite Hea52) in "Hpst".
          assert (Hpc56 : add_vec_int (mword_of_int (KernelSyms.wakeup + 0x52) : mword 64) 4
                          = mword_of_int (KernelSyms.wakeup + 0x56)) by (apply bv_eq; vm_compute; reflexivity).
          iEval (rewrite Hpc56) in "Hpc".
          (* reassemble proc_lock_res via the wakeup transition. *)
          assert (Hnc : (if needs_ctx st then proc_ctx γk (proc_addr k) else emp)%I
                        = proc_ctx γk (proc_addr k))
            by (rewrite Hst_sl needs_ctx_SLEEPING; reflexivity).
          iEval (rewrite Hnc) in "Hctx".
          iDestruct (proc_lock_res_wakeup γk (proc_addr k) ch with "Hpst Hpch Hctx") as "HR".
          (* ---- 0x56 c.j release ---- *)
          iPoseProof (wki_56 with "Htext") as "Hi56".
          assert (H56tgt : add_vec (mword_of_int (KernelSyms.wakeup + 0x56) : mword 64)
                            (sign_extend' 64 (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))))
                          = mword_of_int (KernelSyms.wakeup + 0x2a)) by (apply bv_eq; vm_compute; reflexivity).
          iApply (wp_cj_s root_ppn E Phi (mword_of_int (KernelSyms.wakeup + 0x56))
                    (sign_extend' 21 (concat_vec (mword_of_int 2026 : mword 11) ('b"0"))) _
                    mst2 miev2 mdv2 menv2 (dq:=DfracOwn 1)
                    HN HSIE2 HMPRV2 HSXL2 Hmm2 HPBMTE2 Hmenvval2 ltac:(rewrite H56tgt; vm_compute; reflexivity)
                    with "Hhw Hinv Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Hi56 [-]").
          iIntros "Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile".
          iEval (rewrite H56tgt) in "Hpc".
          iApply ("Hrel" $! M4e with "[%] Hhs Hpriv Hms Hmie Hmdl Hmenv Htlb Hpc Hfile Htok HR").
          repeat split; [exact HM4e_9 | exact HM4e_2 | exact HM4e_4 | exact HM4e_18
                        | exact HM4e_19 | exact HM4e_20 | exact HM4e_21 | exact HdomM4e].
    }
    (* discharge the loop at [fuel := NPROC], [k] (the caller's start index). *)
    iIntros (k M) "%Hk %Hregs Hsm Hgc Htlb #Htext Hpc Hfile Hres Hframe".
    iApply ("Hloop" $! NPROC k M with "[%] [%] [%] Hqexit Hsm Hgc Htlb Htext Hpc Hfile Hres Hframe").
    - lia.
    - exact Hk.
    - exact Hregs.
  Qed.

  (* the prologue's exit register shape [wk_regs .. k] refines the loop's
     entry shape [wk_loop_regs .. k] (NPROC = 64, so proc_addr NPROC = proc_addr 64;
     the extra [ra] constraint is simply dropped). *)
  Lemma wk_regs_loop (M : gmap regidx (mword 64)) (spF sp0 rra rtp chan : mword 64) (k : nat) :
    wk_regs M spF sp0 rra rtp chan k -> wk_loop_regs M spF rtp chan k.
  Proof.
    intros (Hra & Hsp & H9 & H4 & H18 & H19 & H20 & H21 & Hdom).
    unfold wk_loop_regs.
    repeat split; [exact H9 | exact Hsp | exact H4 | exact H18 | exact H19 | exact H20 | exact H21 | exact Hdom].
  Qed.

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan): prologue -> loop (k=0, exiting to  *)
  (* the epilogue) -> return.  The caller provides the callee-save frame     *)
  (* cells, the per-cpu push_off scratch/lock words ([wk_res]), and the      *)
  (* global proc-array lock invariant ([procs_inv]).  The three arithmetic   *)
  (* side conditions ([mycpu] non-null, push_off/pop_off noff round-trip)    *)
  (* are the caller's obligations on the current cpu's bookkeeping.          *)
  (* ===================================================================== *)
  Lemma wp_wakeup (m : gmap regidx (mword 64)) (γs : list gname) (a0f : mword 64)
      (noffv : mword 32) (f7 f6 f5 f4 f3 f2 f1 : bv 64) :
    ↑minstretN ⊆ E -> ↑lockN ⊆ E ->
    (forall r : regidx, r ∈ dom m) ->
    length γs = NPROC ->
    let spF := add_vec (m !!! Regidx (mword_of_int 2 : mword 5))
                 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
    mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5)) = a0f ->
    eq_vec (zero_reg : mword 64) (mycpu_ret (m !!! Regidx (mword_of_int 4 : mword 5))) = false ->
    zopz0zKzJ_s zero_reg (sign_extend' 64 (wk_noff_acq noffv)) = false ->
    wk_noff_rel (wk_noff_acq noffv) = noffv ->
    eq_vec (access_vec_dec (update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
              (sign_extend' 64 (zeros' 12))) 0 ('b"0")) 0) ('b"0") = true ->
    smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
    kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗ gpr_file m -∗
    wk_fcell spF 7 ↦₈ f7 -∗ wk_fcell spF 6 ↦₈ f6 -∗ wk_fcell spF 5 ↦₈ f5 -∗
    wk_fcell spF 4 ↦₈ f4 -∗ wk_fcell spF 3 ↦₈ f3 -∗ wk_fcell spF 2 ↦₈ f2 -∗
    wk_fcell spF 1 ↦₈ f1 -∗
    wk_res γs spF a0f noffv -∗ procs_inv γs -∗
    ( ∀ Mf : gmap regidx (mword 64),
        ⌜ Mf !!! Regidx (mword_of_int 1)  = m !!! Regidx (mword_of_int 1 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 8)  = m !!! Regidx (mword_of_int 8 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 9)  = m !!! Regidx (mword_of_int 9 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 18) = m !!! Regidx (mword_of_int 18 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 19) = m !!! Regidx (mword_of_int 19 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 20) = m !!! Regidx (mword_of_int 20 : mword 5)
        /\ Mf !!! Regidx (mword_of_int 21) = m !!! Regidx (mword_of_int 21 : mword 5)
        /\ Mf !!! Regidx csp_rs1 =
             add_vec spF (sign_extend' 64 (caddi16sp_imm (mword_of_int 4 : mword 6)))
        /\ (forall r : regidx, r ∈ dom Mf) ⌝ -∗
        smode_config γc (DfracOwn 1) -∗ ghost_var γc (1/2) bsie -∗ tlb_inv root_ppn -∗
        kernel_text -∗
        pc_is (update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                 (sign_extend' 64 (zeros' 12))) 0 ('b"0")) -∗ gpr_file Mf -∗
        wk_frame spF (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
          (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
          (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
          (m !!! Regidx (mword_of_int 21 : mword 5)) -∗
        WP (Loop : expr riscv_lang) @ E {{ Phi }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Phi }}.
  Proof.
    intros HN HNl Hdom Hlen spF Hmycpu Hmycpu_nz Hnf_pos Hnf_rt Halign.
    iIntros "Hsm Hgc Htlb #Htext Hpc Hfile Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1 Hres #Hpinv Hcont".
    (* ---- prologue: save frame, set up loop registers, jump to the test ---- *)
    iApply (wp_wakeup_prologue m f7 f6 f5 f4 f3 f2 f1 HN Hdom
              with "Hsm Hgc Htlb Htext Hpc Hfile Hc7 Hc6 Hc5 Hc4 Hc3 Hc2 Hc1 [-]").
    iIntros (M) "%Hwkregs Hsm Hgc Htlb Htextp Hpc Hfile Hframe".
    (* ---- the loop, threaded with the epilogue as its exit continuation ---- *)
    iPoseProof (wp_wakeup_loop γs spF a0f (m !!! Regidx (mword_of_int 4 : mword 5))
                  (m !!! Regidx (mword_of_int 10 : mword 5)) noffv
                  (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                  (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                  (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                  (m !!! Regidx (mword_of_int 21 : mword 5))
                  HN HNl Hlen Hmycpu Hmycpu_nz Hnf_pos Hnf_rt
                  with "Hpinv") as "Hloop".
    iSpecialize ("Hloop" with "[Hcont]").
    { (* Qexit = epilogue at wakeup+0x58 *)
      iIntros (Mexit) "[%Hcsp %Hedom] Hsm Hgc Htlb Htextx Hpc Hfile Hframe".
      iApply (wp_wakeup_epilogue Mexit spF
                (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 8 : mword 5))
                (m !!! Regidx (mword_of_int 9 : mword 5)) (m !!! Regidx (mword_of_int 18 : mword 5))
                (m !!! Regidx (mword_of_int 19 : mword 5)) (m !!! Regidx (mword_of_int 20 : mword 5))
                (m !!! Regidx (mword_of_int 21 : mword 5))
                HN Hcsp Hedom Halign
                with "Hsm Hgc Htlb Htextx Hpc Hfile Hframe Hcont"). }
    iApply ("Hloop" $! 0%nat M with "[%] [%] Hsm Hgc Htlb Htextp Hpc Hfile Hres Hframe").
    - unfold NPROC. lia.
    - exact (wk_regs_loop M spF (m !!! Regidx (mword_of_int 2 : mword 5))
               (m !!! Regidx (mword_of_int 1 : mword 5)) (m !!! Regidx (mword_of_int 4 : mword 5))
               (m !!! Regidx (mword_of_int 10 : mword 5)) 0 Hwkregs).
  Qed.

End ProcInv.

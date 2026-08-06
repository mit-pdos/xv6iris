(* CodeWakeupAux.v -- the per-process spinlock invariant of xv6's [struct proc],
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
Require Import FdSlots.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import RegFile.
Require Import InstrBytes RiscvFetchExec KernelText.
Require Import WpLock.
Require Import WpMmodeLeafBase.
Require Import VcGen.
Require Import RiscvExec RiscvExtras WpDecode WpRvcBridge.
From Kernel Require Import KernelSyms KernelInstrs.
Require Import WpDecodeBridge.
Require Export WpSmodeLeafBase.
Require Export ProcGeom.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
Require Import CodeWakeup.
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
(* 0x80001f5c addi s1,s1,-2016 *)

(* 0x80001f68 addi s2,s2,532 *)

(* 0x80001f78 beq s1,s2,+36 *)

(* 0x80001f80 beq a0,s1,-12 *)

(* 0x80001f8c bne a5,s3,-30 *)

(* 0x80001f92 bne a5,s4,-36 *)

(* 0x80001f96 sw s5,24(s1) *)

(* 0x80001f70 jal release (-4846) *)

(* 0x80001f7c jal myproc (-1670) *)

(* 0x80001f86 jal acquire (-5004) *)

(* ---- compressed instructions (misa.C + rvc_oneshot; ext_decode_compressed) ---- *)
(* 0x80001f60 c.li s3,2 ; 0x80001f62 c.li s5,3 *)

(* 0x80001f8a c.lw a5,24(s1): [cdec_4c9c] -- shared, see KernelRvcDecode.v *)
(* 0x80001f90 c.ld a5,32(s1) *)

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
  Context `{GEN : GenId} `{CID : CpuId}.

  (* c.li rd, imm  ==  addi rd, x0, sext(imm) : writes sext(imm) into rd.
     Mirrors wp_caddi_gpr_s_config_pt but with rs1 = x0 (so the value is the
     immediate, not rd+imm).  Discharged through wp_gpr_write_s_config_pt. *)

  (* ---- instruction fact builders (verbatim from WpSwtchVc) ---- *)

  (* ---- prologue ---- *)

  (* ---- loop / release path ---- *)

  (* ---- epilogue ---- *)

  (* the prologue block's [instr] facts, assembled from the [wki_*] templates. *)

  (* the epilogue block's [instr] facts, assembled from the [wki_*] templates. *)

End WkLeaves.

(* ======================================================================= *)
(* Leaf lemmas specific to wakeup's instruction mix that were not already   *)
(* available: the compressed [c.li rd, imm] (ADDI from x0).                  *)

Section WkScfgLeaves.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

End WkScfgLeaves.

(* The per-proc lock invariant ([proc_lock_res] / [procs_inv]), the parked
   context obligation ([proc_ctx]) and their intro/elim/wakeup lemmas moved
   to SchedCtx.v (built on the sconf-γ swtch protocol), superseding the old
   smode-config / [contains_lock]-based versions that used to live here.
   CodeWakeup keeps only the decode/leaf/loop-arithmetic content below. *)
Section ProcInv.
  Context `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

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

  (* Nothing per-proc rides with the scan any more: both words of every proc
     lock are inside its [lock_inv] (WpLock.v), and what acquire needs beside
     the lock itself is only [panic_wp] -- persistent, so one copy serves all
     64 iterations. *)

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

  (* [csp_rs1] (the c.*sp base encoding) is register x2 (sp). *)

  (* the noff word as rewritten by acquire's push_off (noff+1, truncated to 32)
     and, one round later, by release's pop_off (noff-1).  The loop threads the
     entry value [noffv] through an acquire/release pair each iteration; the two
     hypotheses [wk_noff_acq >s 0] and [round-trip = noffv] let it close. *)

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

  (* ===================================================================== *)
  (* Whole-function WP for wakeup(chan): prologue -> loop (k=0, exiting to  *)
  (* the epilogue) -> return.  The caller provides the callee-save frame     *)
  (* cells, the per-cpu push_off scratch/lock words ([wk_res]), and the      *)
  (* global proc-array lock invariant ([procs_inv]).  The three arithmetic   *)
  (* side conditions ([mycpu] non-null, push_off/pop_off noff round-trip)    *)
  (* are the caller's obligations on the current cpu's bookkeeping.          *)
  (* ===================================================================== *)

End ProcInv.

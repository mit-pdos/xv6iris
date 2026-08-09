(* UmodeSyscall.v -- the xv6 SYSCALL PROTOCOL layer of the verified
   user-execution tier (claude-notes/projects/user-verified.md).

   The semantics of a syscall belongs to the KERNEL, not to any user
   program: every process that executes `ecall` with a7 = SYS_sync is owed
   the same service.  So the per-syscall arms and the number -> semantics
   table live here, program-generic; a process's [usys_protocol]
   (UmodeCap.v) is just this table read through [usys_protocol_of], and a
   program's Spec<Prog>Prog.v never restates syscall semantics.

   TODAY'S SEMANTIC DEPTH.  The kernel side (usertrap -> syscall() -> the
   sys_* bodies) is unproven, and no syscall has a real semantic spec yet,
   so the table carries only the two COARSE shapes the first verified
   programs need -- and the arm type is an Inductive precisely so that a
   syscall acquiring a real specification (a precondition, a memory
   effect, a constrained return value) extends it rather than reworking
   any consumer:

     [UsysPureRet]  the syscall returns: a0 := an ARBITRARY value, every
                    other register / the image / pc+4 intact, on an
                    arbitrary hart.  (The xv6 trap path restores all GPRs
                    from the trapframe except a0, and bumps epc by 4.)
     [UsysNoRet]    the syscall never returns to this process (exit).
     [UsysUnused]   no semantics stated: the arm is [False], so a verified
                    process simply cannot be proven to invoke it (and the
                    kernel's eventual obligation for it is vacuous). *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import UserPtTree UserExec.
Require Import UmodeCap UmodeAbi.
Local Open Scope Z_scope.
Import Defs.

(* ===================================================================== *)
(* §1 The xv6 syscall numbers (kernel/syscall.h).                          *)
(* ===================================================================== *)

Definition SYS_fork   : Z := 1.
Definition SYS_exit   : Z := 2.
Definition SYS_wait   : Z := 3.
Definition SYS_pipe   : Z := 4.
Definition SYS_read   : Z := 5.
Definition SYS_kill   : Z := 6.
Definition SYS_exec   : Z := 7.
Definition SYS_fstat  : Z := 8.
Definition SYS_chdir  : Z := 9.
Definition SYS_dup    : Z := 10.
Definition SYS_getpid : Z := 11.
Definition SYS_sbrk   : Z := 12.
Definition SYS_pause  : Z := 13.
Definition SYS_uptime : Z := 14.
Definition SYS_open   : Z := 15.
Definition SYS_write  : Z := 16.
Definition SYS_mknod  : Z := 17.
Definition SYS_unlink : Z := 18.
Definition SYS_link   : Z := 19.
Definition SYS_mkdir  : Z := 20.
Definition SYS_close  : Z := 21.
Definition SYS_sync   : Z := 22.

(* ===================================================================== *)
(* §2 The coarse per-syscall semantic shapes, and the arm each denotes.    *)
(* ===================================================================== *)

Inductive usys_sem : Type :=
  | UsysPureRet
  | UsysNoRet
  | UsysUnused.

Section UmodeSyscall.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId}.
  Context (C : ucfg) (pt : uptd).

  (* what the process supplies at an [ecall] whose number has shape [s] --
     for a returning syscall, the resume continuation (hart re-bound, a0
     arbitrary, pc+4); for a non-returning one, nothing. *)
  Definition usys_arm (s : usys_sem) (g : regfile) (va : mword 64)
      (M : gmap Z (bv 8)) : iProp Σ :=
    match s with
    | UsysPureRet =>
        (∀ (CID : CpuId) (ret : mword 64),
           uv_run C pt M (<[Regidx a0_idx := ret]> g) (add_vec_int va 4) -∗
           WP (Loop : expr riscv_lang))%I
    | UsysNoRet => emp%I
    | UsysUnused => False%I
    end.

  (* a protocol from a number -> shape table *)
  Definition usys_protocol_of (tbl : Z -> usys_sem) : usys_protocol Σ :=
    fun n g va M Φ => usys_arm (tbl n) g va M.

End UmodeSyscall.

(* ===================================================================== *)
(* §3 THE xv6 TABLE: the shapes stated so far.  Extend an entry (and the   *)
(* [usys_sem] type, as needed) when a syscall acquires a real semantic     *)
(* spec; consumers go through [xv6_sys_protocol] and never change.         *)
(* ===================================================================== *)

Definition xv6_sys_sem (n : Z) : usys_sem :=
  if bool_decide (n = SYS_sync) then UsysPureRet
  else if bool_decide (n = SYS_exit) then UsysNoRet
  else UsysUnused.

Definition xv6_sys_protocol `{!riscvGS Σ} `{GEN : GenId}
    (C : ucfg) (pt : uptd) : usys_protocol Σ :=
  usys_protocol_of C pt xv6_sys_sem.

(* the two dispatch facts stub proofs use *)
Lemma xv6_sys_sem_sync : xv6_sys_sem SYS_sync = UsysPureRet.
Proof. reflexivity. Qed.
Lemma xv6_sys_sem_exit : xv6_sys_sem SYS_exit = UsysNoRet.
Proof. reflexivity. Qed.

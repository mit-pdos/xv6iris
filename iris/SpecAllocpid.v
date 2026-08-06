(* SpecAllocpid.v -- the public interface of allocpid() (kernel/proc.c),
   stated independently of its proof.

     int allocpid() {
       int pid;
       acquire(&pid_lock);
       pid = nextpid;
       nextpid = nextpid + 1;
       release(&pid_lock);
       return pid;
     }

   @ KernelSyms.allocpid = 0x800019d0, fifteen instructions: a 32-byte
   ra/s0/s1 frame, acquire(&pid_lock), [lw s1,0(a5)] / [addiw a4,s1,1] /
   [sw a4,0(a5)] on <nextpid>, release, [c.mv a0,s1].

   WHAT THE CONTRACT SAYS ABOUT THE RESULT: nothing.  The counter is a plain
   [int] that the code lets overflow, and no consumer needs more -- allocproc
   stores whatever comes back into [p->pid] and its own postcondition
   quantifies the pid existentially.  Stating uniqueness would need a ghost
   history of every pid ever issued, which nothing in the tree consumes.
   So the whole contract is: the counter's lock is taken and released
   (interrupt level net zero), and callee-saved registers survive.

   The lock's resource is defined here, at the one place that names it:
   [nextpid_res] is the counter cell with its value existential, which is all
   the lock protects.  procinit produces the lock's raw fields and its
   caller seals them into this [is_lock] (the same division iinit draws for
   the inode sleeplocks). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.


(* the two globals allocpid touches *)
Definition alp_pid_lock : mword 64 := mword_of_int KernelSyms.pid_lock.
Definition alp_nextpid  : mword 64 := mword_of_int KernelSyms.nextpid.

Section SpecAllocpid.
  Context `{!riscvGS Σ}.

  (* everything <pid_lock> protects: the counter, value unconstrained. *)
  Definition nextpid_res : iProp Σ :=
    (∃ v : mword 32, alp_nextpid ↦₄ v)%I.

End SpecAllocpid.

Definition wp_allocpid_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γp : gname)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.allocpid in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for acquire's / release's *)
  (14 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γp alp_pid_lock "nextpid"%string nextpid_res -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ALLOCPID.
  Parameter wp_allocpid_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γp : gname)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool),
      wp_allocpid_sconf_body Φ γp m av n eb p C b.
End ALLOCPID.

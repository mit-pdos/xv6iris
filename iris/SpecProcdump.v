(* SpecProcdump.v -- the public interface of procdump(), stated independently
   of its proof.

     void procdump(void) {
       static char *states[] = { [UNUSED] "unused", [USED] "used",
         [SLEEPING] "sleep ", [RUNNABLE] "runble", [RUNNING] "run   ",
         [ZOMBIE] "zombie" };
       struct proc *p;  char *state;

       printk("\n");
       for (p = proc; p < &proc[NPROC]; p++) {
         if (p->state == UNUSED) continue;
         if (p->state >= 0 && p->state < NELEM(states) && states[p->state])
           state = states[p->state];
         else
           state = "???";
         printk("%d %s %s", p->pid, state, p->name);
         printk("\n");
       }
     }

   @ KernelSyms.procdump, 164 bytes / 52 instructions: an 80-byte frame
   holding ra/s0 and s1..s7, s1 the cursor (at &p->name, i.e. p + 344 -- gcc
   biases it so the three field reads are negative displacements off it), s2
   the end sentinel, s3 "???", s4 "\n", s5 "%d %s %s", s6 = 5, s7 the
   [states] table.  One loop, three printk calls.

   ====================================================================
   WHAT procdump READS, AND WHY ITS PRECONDITION LOOKS LIKE THIS
   ====================================================================

   procdump takes NO LOCK -- that is deliberate in xv6 ("no lock to avoid
   wedging a stuck machine further") and it is the whole difficulty of
   specifying it.  It reads three fields of every slot:

     p->state  (+24)   lock-protected and genuinely mutable
     p->pid    (+48)   half in [SchedCtx.proc_pub], half in [ProcInv.proc_priv]
     p->name   (+344)  exclusively owned by whoever is RUNNING the process

   -- so [design/proc-struct.md]'s five sharing disciplines give procdump the
   right to read NONE of them.  In separation logic a load needs a fraction of
   the cell, and a fraction is exactly what forbids the concurrent write that
   makes this code racy.  A [%s] argument is worse than an ordinary racy read:
   printk WALKS the string, so [p->name] must be stably owned across the call,
   not merely read atomically once.  No invariant-based "peek" resource can
   supply that.

   So the honest precondition is a read-SHARE of the three fields of all 64
   slots, at fractions the caller chooses, handed back untouched:

       procdump_view  =  [∗ list] j < NPROC, proc_dump_slot (proc_addr j)

   That is the contract, and its being unsatisfiable from anything currently
   in the tree is not a gap in the spec -- it IS the statement that procdump
   is racy.  Discharging it would mean making [state]/[pid]/[name]
   permanently read-shared, which allocproc, kfork (it [safestrcpy]s the
   child's name) and kexec each rule out.  consoleintr's ^P path therefore
   cannot link against this contract; see claude-notes/projects/procdump.md.

   WHAT THE VIEW DOES *NOT* SAY, and why that is the good news: nothing about
   the VALUES.  Every 32-bit [p->state] is handled by the compiled code --
   0 skips the slot, 1..5 index [states], anything else (including negative,
   which the [bltu] against 5 catches together with the C's [p->state >= 0]
   test) prints "???" -- so the state is existential, the pid is existential
   (it is a [%d] vararg and nothing reads it back), and the name needs only
   to BE a C string ([nonul]).  The view is thus a pure read-permission
   claim with no coherence obligation, which is what lets a caller supply it
   at any fractions and get the same thing back.

   ====================================================================
   THE REST
   ====================================================================

   - The four string literals and the [states] table itself come out of
     [kernel_data] (persistent, [↦ₛ□] / [↦ₘ□]), so none of them is a
     premise: procdump's format strings and its six state names are image
     bytes, not caller state.
   - printk runs on its GENERAL path here (procdump is not panic code), so
     the callee is [SpecPrintk]: its persistent credential [printk_env]
     plus its contract carried as a Coq HYPOTHESIS
     ([SpecPrintk.printk_gen_contract]) rather than as a functor argument
     -- the shape SpecBalloc.v uses, and for the same reason: PRINTK_GEN's
     only instance is LinkPrintk's [Axiom], and taking it as a functor
     would drag that axiom into procdump's [Print Assumptions] and into
     every caller's.
   - [cpu_own 0 eb p C b] is threaded net-zero (printk's acquire/release
     pair leaves the interrupt level as it found it), and [panic_wp_any] is
     carried because that acquire needs it.  No [procs_inv]: procdump takes
     no proc lock, which is the one respect in which it is EASIER than
     wakeup and kkill.
   - K >= 48: procdump's own ten slots plus printk's thirty-eight.

   Requires only the definitional layer plus SpecPrintk.v's vocabulary --
   never a [Proof*] file. *)
From Stdlib Require Import ZArith Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import PrintkFmt.
Require Import PanicStub.
Require Import SpecPrintk.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

Section ProcdumpView.
  Context `{!riscvGS Σ}.

  (* ------------------------------------------------------------------ *)
  (* ONE slot's worth of the racy-debug read permission.                 *)
  (*                                                                     *)
  (* The three fractions are INDEPENDENT and existential, and so are the *)
  (* two values: procdump neither relates them nor reports them, so a    *)
  (* caller may hand over whatever read-shares it happens to have, and   *)
  (* the same proposition comes back.  The one non-permission conjunct   *)
  (* is [nonul nm] -- p->name must actually be a C string, which is what *)
  (* printk's "%s" walk needs and what safestrcpy's NUL-termination      *)
  (* makes true of every live slot.                                      *)
  (* ------------------------------------------------------------------ *)
  Definition proc_dump_slot (pa : mword 64) : iProp Σ :=
    (∃ (dqs dqp dqn : dfrac) (st pid : mword 32) (nm : string),
       ⌜ nonul nm = true ⌝ ∗
       p_state pa  ↦₄{ dqs } st ∗
       p_pid   pa  ↦₄{ dqp } pid ∗
       p_name  pa 0 ↦ₛ{ dqn } nm)%I.

  (* The whole table.  [seq 0 NPROC] binds the INDEX as the element, so the
     big-op splits at a cursor with [seq_app] -- which is exactly the shape
     the scan's loop invariant wants (done prefix ∗ remaining suffix). *)
  Definition procdump_view : iProp Σ :=
    ([∗ list] j ∈ seq 0 NPROC, proc_dump_slot (proc_addr j))%I.

End ProcdumpView.

Definition wp_procdump_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr : gname) (γd : uart_names) (γv : disk_names)
    (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let pcE : mword 64 := mword_of_int KernelSyms.procdump in
  let ra0 := m !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (* ten slots of its own, forty-eight for printk (printk_stack) *)
  (58 <= K)%nat ->
  (* the callee, as a hypothesis and not a functor -- see the header *)
  printk_gen_contract γpr γd γv ->
  (* procdump takes no lock of its own (the header's whole point); its one
     callee, printk, is entered at rank "pr" -- the lowest (only) rank this
     cone touches, so this is the whole order premise. *)
  locks_below lks "pr" ->
  sie_cap_gpr m K b p -∗
  (* the interrupt level is left exactly as found: printk's acquire/release *)
  cpu_own 0%nat eb p C b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  printk_env γpr γd γv -∗
  (* THE RACY-DEBUG READ PERMISSION (see the header) *)
  procdump_view -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      sie_cap_gpr mf K b p -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
      cpu_own 0%nat eb p C b lks -∗
      procdump_view -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PROCDUMP.
  Parameter wp_procdump_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names)
      (m : regfile) (K : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) (lks : gset string),
      wp_procdump_sconf_body γpr γd γv m K eb p C b lks.
End PROCDUMP.

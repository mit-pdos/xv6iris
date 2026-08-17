(* SpecDevintr.v -- the public interface of devintr(), stated independently of
   its proof.  Requires only the definitional layer and its callees' Spec files
   -- never a whole-function proof file.

     int devintr(void) {
       uint64 scause = r_scause();
       if (scause == 0x8000000000000009L) {          // supervisor external, via PLIC
         int irq = plic_claim();
         if      (irq == UART0_IRQ)   uartintr();
         else if (irq == VIRTIO0_IRQ) virtio_disk_intr();
         else if (irq)                printk("unexpected interrupt irq=%d\n", irq);
         if (irq) plic_complete(irq);
         return 1;
       } else if (scause == 0x8000000000000005L) {   // timer
         clockintr();
         return 2;
       } else return 0;
     }

   @ KernelSyms.devintr = 0x8000250c, 39 instructions, a 32-byte frame
   (ra/s0 always, s1 SHRINK-WRAPPED into the PLIC arm).

   THIS IS THE MACHINE'S INTERRUPT DEMULTIPLEXER, and the contract is
   correspondingly the point at which the whole device complement becomes ONE
   object.  Every credential devintr needs is PERSISTENT, so they are bundled
   as [devintr_caps] rather than listed: a caller threads one hypothesis, and
   adding a device to the machine changes the bundle rather than every
   contract on the trap path.

   THE RETURN VALUE IS A FUNCTION OF scause, and the spec says so
   ([devintr_ret]).  That is why the [scause] cell is threaded EXPLICITLY and
   at a PINNED value rather than taken from [IntrDefs.trap_csrs], whose scause
   is existential: a caller receiving only "the result is 0, 1 or 2" could not
   tell which, and the three-way branch is the entire content of the function.
   The cell comes back untouched (nothing devintr calls owns it, and with
   interrupts off no trap rewrites it).  [dq] is any fraction: the read pins
   the value and does not need the cell exclusively.

   THE printk ARM IS DEAD, and that is what [PlicPlan.plic_claim_ret_ok]
   exists for: under the kernel's PLIC plan a claim can only return 0,
   [uart_irq_id] or [virtio_irq_id], so the two [beq]s above it are exhaustive
   on the nonzero cases and the [c.bnez a4] at +0x42 provably falls through.
   Nothing on this path calls printk -- which matters, because only printk's
   PANIC path is proved.

   INTERRUPTS ARE OFF ([b = false]), and not as a convenience: plic_claim,
   plic_complete and clockintr are each [false]-ONLY (they call cpuid()
   unbracketed, and cpuid reads tp mid-body), and clockintr's [tick_keeper] is
   hart-indexed.  xv6 agrees -- devintr runs only from usertrap()/kerneltrap(),
   the latter of which PANICS if it finds interrupts enabled.  So the contract
   carries no [wp_next] wrapper ([wp_next_off] would collapse it anyway).

   WHAT THE CONTRACT DELIBERATELY DOES NOT SAY: anything about what the
   handlers did.  A completion reaches the process that was waiting for it
   through [disk_res] / [tx_res] / the proc array, never through devintr's
   postcondition -- so the post is just "callee-saved registers preserved, a0
   = [devintr_ret scause], everything handed back". *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import FdSlots.
Require Import ProcGeom CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto WpUart DiskInv.
Require Import TimerCap.
Require Import SpecClockintr.
Require Import SpecConsoleintr.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.


(* ===================================================================== *)
(* The two causes devintr recognises.                                     *)
(* ===================================================================== *)

(* scause for a supervisor EXTERNAL interrupt: the interrupt bit (63) plus
   cause 9.  The code materialises it as [li -1; slli 63; addi 9]. *)
Definition SCAUSE_SEXT : Z := 0x8000000000000009.

(* ... and for a supervisor TIMER interrupt: bit 63 plus cause 5. *)
Definition SCAUSE_STIMER : Z := 0x8000000000000005.

(* devintr's return value, as the C comment gives it: 1 for "some other
   device" (the PLIC arm), 2 for a timer interrupt, 0 for "not recognised".
   The tests are in source order -- external first, then timer. *)
Definition devintr_ret (sc : mword 64) : mword 64 :=
  if eq_vec sc (mword_of_int SCAUSE_SEXT : mword 64)
  then (mword_of_int 1 : mword 64)
  else if eq_vec sc (mword_of_int SCAUSE_STIMER : mword 64)
       then (mword_of_int 2 : mword 64)
       else (mword_of_int 0 : mword 64).

(* ===================================================================== *)
(* The device complement, as one persistent credential.                   *)
(* ===================================================================== *)

Section DevintrCaps.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  (* Everything the five handlers ask of a caller, in the order the branches
     reach them:

       [dev_inv]      the memory-mapped device invariant (UART + PLIC +
                      virtio-mmio), which plic_claim/plic_complete open around
                      their MMIO transactions and which the UART leaves need.
                      IT IS ALSO ALL uartintr ITSELF WANTS: ae96fd0's handler
                      takes no lock and moves no device ghost;
       [console_caps]  what uartintr PASSES ON.  consoleintr is proven now, and
                      its proof cannot be silent about the echo: it takes
                      cons.lock and, through consputc, tx_lock.  So the two
                      lock credentials come back into this bundle -- bundled,
                      with both ghost names existential, so this is one
                      conjunct and no parameter (SpecConsoleintr.v).  NOTHING
                      CONSTRUCTS IT YET: see claude-notes/projects/console.md
                      for the boot wiring it waits on;
       [disk_geom]    +
       [is_lock ... disk_res]
                      virtio_disk_intr's;
       [timer_cap]    +
       [tick_keeper]  clockintr's: the persistent mcounteren/stimecmp
                      capability every hart needs, and the tick machinery only
                      hart 0 does (a disjunction the other harts discharge for
                      free);
       [procs_inv]    the proc array's locks -- wakeup, reached from three of
                      the handlers;

     ALL PERSISTENT, so the bundle is threaded and never consumed, and the
     postcondition does not mention it. *)
  Definition devintr_caps (γu : uart_names) (γv : disk_names)
      (γdk γtl : gname)  (γs : list gname)
      (pd pav pu : mword 64) : iProp Σ :=
    ( dev_inv γu γv ∗
      console_caps γu ∗
      disk_geom γv pd pav pu ∗
      is_lock γdk d_lock "virtio_disk"%string (disk_res γv pd pav pu) ∗
      timer_cap ∗
      tick_keeper (kt := kt) γtl γs ∗
      procs_inv (kt := kt) γs )%I.

  Global Instance devintr_caps_persistent γu γv γdk γtl γs pd pav pu :
    Persistent (devintr_caps γu γv γdk γtl γs pd pav pu).
  Proof. rewrite /devintr_caps. apply _. Qed.

End DevintrCaps.

(* devintr's own frame is 4 slots; the deepest callee is uartintr at
   [SpecUartintr.uartintr_stack] = 36 (virtio_disk_intr wants 22, clockintr
   20, plic_complete 6, plic_claim 4). *)
Notation devintr_stack := (52%nat) (only parsing).
Definition wp_devintr_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
    (γs : list gname) (pd pav pu : mword 64)
    (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64)
    (dq : dfrac) (sc : mword 64) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.devintr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  length γs = NPROC ->
  (* the transient noff increments inside the handlers' acquire/wakeup pairs
     stay in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (devintr_stack <= av)%nat ->
  (* devintr itself acquires nothing, but it dispatches three cones and the
     premise has to be stated at the MINIMUM rank over all of them -- a bound
     is STRENGTHENED by lowering it, and [locks_below_mono] only RAISES, so a
     bound at "time" would not deliver the one uartintr wants.  The three:
     clockintr -> tickslock ("time", 8); virtio_disk_intr -> "virtio_disk"
     (9); uartintr -> consoleintr -> cons.lock ("cons", 5).  Minimum is 5.
     Trivial at every real call site: devintr always runs at trap entry,
     where [lks = ∅]. *)
  locks_below lks "cons" ->
  sie_cap_gpr kt m av false p -∗
  cpu_own lvl eb p false lks -∗
  kernel_text -∗ pc_is pcE -∗
  scause ↦ᵣ{dq} sc -∗
  devintr_caps (kt := kt) γu γv γdk γtl γs pd pav pu -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf /\ mf !!! Regidx (mword_of_int 10 : mword 5) = devintr_ret sc ⌝ -∗
      sie_cap_gpr kt mf av false p -∗
      cpu_own lvl eb p false lks -∗
      scause ↦ᵣ{dq} sc -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type DEVINTR.
  Parameter wp_devintr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (γu : uart_names) (γv : disk_names) (γdk γtl : gname)
      (γs : list gname) (pd pav pu : mword 64)
      (m : regfile) (av lvl : nat) (eb : bool) (p : mword 64)
      (dq : dfrac) (sc : mword 64) (lks : gset string),
      wp_devintr_sconf_body kt γu γv γdk γtl γs pd pav pu m av lvl eb p dq sc lks.
End DEVINTR.

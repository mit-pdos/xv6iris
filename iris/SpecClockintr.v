(* SpecClockintr.v -- the public interface of clockintr, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void clockintr(void) {
       if (cpuid() == 0) {
         acquire(&tickslock); ticks++; wakeup(&ticks); release(&tickslock);
       }
       // ask for the next timer interrupt; this also clears the current one
       w_stimecmp(r_time() + 1000000);
     }

   Two halves, and the contract keeps them apart.

   THE TIMER TAIL runs on EVERY hart: it reads [time] and writes [stimecmp],
   which at Supervisor need mcounteren.TM = 1 plus menvcfg.STCE (the latter
   already pinned by [sconf]).  Both arrive in the PERSISTENT [timer_cap]
   (TimerCap.v) -- the TM pin plus an invariant holding the [stimecmp] cell --
   so a caller passes it and has nothing to thread back out.  That is sound
   because no deadline a caller could name survives the call anyway: the value
   written is [r_time() + 1000000] and mtime lives in the value-agnostic
   [clock_inv] (MinstretInv.v).  Note what this makes invisible: clearing the
   pending timer interrupt IS this store (the tick recomputes mip.STIP :=
   stimecmp <=u mtime), but mip is likewise unowned and unpinned, so
   "the interrupt is acknowledged" is not a statement this logic can make --
   the interrupt machinery reads mip straight off the step state and is
   correct for any value of it.

   THE TICK BLOCK runs only on the hart whose id is 0, so the resources it
   needs ride under [tick_keeper], a disjunction keyed on the ambient hart:
   a hart that is not the tick keeper discharges it for free ([iLeft]), and
   hart 0 supplies the tickslock (with its free cpu field) and the proc
   array's wakeup cells.  ONE spec then serves every hart -- no per-hart case
   split leaks out into devintr/kerneltrap -- and the tick machinery is not
   demanded of a hart that provably never touches it.  Nothing is said about
   the counter: the lock protects [ticks_res] (TicksInv.v), the cell at an
   ARBITRARY value, and ticks++ re-establishes exactly that.

   Interrupt/noff bookkeeping is acquire/release's and is order-balanced here,
   so the spec never mentions [arm_pay]; the level returns to [n].
   Calls no per-process state, but acquire/wakeup pin tp = [cid_word]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import HartTp.
Require Import FdSlots.
Require Import CpuOwn.
Require Import WpLock.
Require Import TicksInv.
Require Import TimerCap.
Require Import SchedCtx.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Section SpecClockintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* "this hart keeps time": the branch clockintr tests, [cpuid() == 0]. *)
  Definition tick_hart : bool := eq_vec (cid_word : mword 64) (zero_reg : mword 64).

  (* the tick machinery, owned by the tick keeper (see the header).
     HART-INDEXED, through [tick_hart]'s [cid_word] -- which is why this
     contract is stated at [b = false] and not generically; see the note on
     [wp_clockintr_sconf_body]. [panic_wp_any] rather than [panic_wp] because
     the acquire/wakeup arms it discharges are stated hart-generically. *)
  Definition tick_keeper (Φ : mval -> iProp Σ)
      (γl : gname) (γs : list gname) : iProp Σ :=
    ( ⌜ tick_hart = false ⌝
    ∨ ( is_tickslock γl ∗
        procs_inv Φ γs ∗
        panic_wp_any ) )%I.

End SpecClockintr.

(* INTERRUPTS OFF, for two independent reasons -- neither of which is a
   convenience, and the contract was b-GENERIC until the explicit-CPUID sweep
   made them checkable.

   (1) clockintr CALLS cpuid(), at KernelSyms.clockintr+0x08, and does not bracket the call in
   its own push_off/pop_off.  cpuid() is stated at [b = false] because it
   reads tp mid-body (see the porting guide), so the constraint propagates UP
   the call graph: a caller that invokes cpuid() unbracketed inherits it.
   There is no way to reach [false] from a generic [b] here.

   (2) [tick_keeper] is HART-INDEXED -- [tick_hart] names [cid_word] -- so it
   cannot ride a generic-[b] [wp_next].  At [b = true] the left disjunct
   "the ENTRY hart is not hart 0" says nothing about the RESUMED hart, and no
   transport exists or could exist.  The whole proof shape depends on this
   too: the [cpuid() == 0] case split is on the ambient hart, which is only
   sound while the hart cannot move.

   xv6 agrees on both counts: clockintr runs only from devintr, inside the
   trap handler, with SIE already off.  Stated at the literal [false] there is
   no [wp_next] wrapper at all ([wp_next_off] would collapse it). *)
Definition wp_clockintr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (γs : list gname)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.clockintr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* acquire's transient noff increments (one for the tickslock, one inside
     wakeup's per-proc acquire) stay in int range *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (20 <= av)%nat ->
  sie_cap_gpr m av false p -∗
  cpu_own n eb p C false -∗
  kernel_text -∗ pc_is pcE -∗
  timer_cap -∗
  tick_keeper Φ γl γs -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av false p -∗
      cpu_own n eb p C false -∗
      pc_is ret_tgt -∗
      tick_keeper Φ γl γs -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CLOCKINTR.
  Parameter wp_clockintr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (γs : list gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_clockintr_sconf_body Φ γl γs m n eb p C av.
End CLOCKINTR.

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
   so the spec never mentions [trap_csrs_pay]; the level returns to [n].
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
Require Import FdSlots.
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import TicksInv.
Require Import TimerCap.
Require Import SchedCtx.
Require Import SpecPanic.
Require Import ProcGeom.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation CI := KernelSyms.clockintr.

Section SpecClockintr.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ}.
  Context `{CID : CpuId}.

  (* "this hart keeps time": the branch clockintr tests, [cpuid() == 0]. *)
  Definition tick_hart : bool := eq_vec (cid_word : mword 64) (zero_reg : mword 64).

  (* the tick machinery, owned by the tick keeper (see the header). *)
  Definition tick_keeper (γ : gname) (Φ : mval -> iProp Σ)
      (γl : gname) (γs : list gname) : iProp Σ :=
    ( ⌜ tick_hart = false ⌝
    ∨ ( is_tickslock γl ∗
        procs_inv Φ γs ∗
        panic_wp ) )%I.

End SpecClockintr.

Definition wp_clockintr_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γs : list gname)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.clockintr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the hart id is the ambient CpuId (acquire/wakeup's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* acquire's transient noff increments (one for the tickslock, one inside
     wakeup's per-proc acquire) stay in int range *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  (20 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  timer_cap -∗
  tick_keeper γ Φ γl γs -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ n eb p C -∗
      pc_is ret_tgt -∗
      tick_keeper γ Φ γl γs -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type CLOCKINTR.
  Parameter wp_clockintr_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (γs : list gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_clockintr_sconf_body γ Φ γl γs m n eb p C av.
End CLOCKINTR.

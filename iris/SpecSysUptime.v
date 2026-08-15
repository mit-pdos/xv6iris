(* SpecSysUptime.v -- the public interface of SysUptime, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     uint64 sys_uptime(void) {
       uint xticks;
       acquire(&tickslock); xticks = ticks; release(&tickslock);
       return xticks;
     }

   The contract: given the tickslock ([is_tickslock], TicksInv.v -- the lock
   over the tick-counter cell at an arbitrary value) and its free cpu field,
   sys_uptime returns SOME 32-bit tick value, zero-extended to 64 bits (the
   [(uint)] return type: the body's slli/srli-by-32 pair), preserves every
   callee-saved register, and gives the cpu field back zeroed.  The value is
   universally quantified in the continuation -- with an invariant that says
   nothing about ticks, nothing more can be said, and a caller must accept any
   reading.  Interrupt/noff bookkeeping is acquire's: the count returns to [n]
   and no [arm_pay] escapes.  Calls no per-process state, but acquire
   pins tp = [cid_word]. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import WpLock.
Require Import PanicStub.
Require Import TicksInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.


Definition wp_sys_uptime_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_uptime in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the hart id is the ambient CpuId (acquire/release's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* acquire's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (14 <= av)%nat ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "time"'s -- sys_uptime acquires and releases [tickslock] in the same
     call, so this contract is BALANCED and [lks] is unchanged end to end. *)
  locks_below lks "time" ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_tickslock γl -∗
  panic_wp_any -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (t : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 t ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSUPTIME.
  Parameter wp_sys_uptime_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_sys_uptime_sconf_body γl m n eb p av b lks.
End SYSUPTIME.

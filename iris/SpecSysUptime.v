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
   and no [trap_csrs_pay] escapes.  Calls no per-process state, but acquire
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
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import TicksInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation SU := KernelSyms.sys_uptime.

Definition wp_sys_uptime_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_uptime in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the hart id is the ambient CpuId (acquire/release's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* acquire's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (14 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  is_tickslock γl -∗
  tickslock_cpu ↦₈ (zero_reg : mword 64) -∗
  ( ∀ (mf : regfile) (t : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 t ⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ n eb p C -∗
      pc_is ret_tgt -∗
      tickslock_cpu ↦₈ (zero_reg : mword 64) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SYSUPTIME.
  Parameter wp_sys_uptime_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_sys_uptime_sconf_body γ Φ γl m n eb p C av.
End SYSUPTIME.

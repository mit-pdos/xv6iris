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
   and no [arm_pay] escapes.  Calls no per-process state, and takes NO tp
   premise -- see the note on that at the contract itself. *)
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
Require Import RiscvExtras.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import LockRank.
Require Import TicksInv.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Definition wp_sys_uptime_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname)
    (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_uptime in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* NO tp PREMISE.  The hart id is the ambient [CpuId], and [tp]'s true
     value at this hart is that id BY CONSTRUCTION -- every register-file
     resource reads through [HartTp.rget], whose [tp] case is
     [rget_tp : rget m Rtp = cid_word_of cpu_id], proved by [upd_eq] with no
     hypothesis at all.  Stating it as [m !!! Regidx Rtp = cid_word] instead
     made it a claim about the CALLER's map, which is (a) not what any leaf
     reads and (b) unsatisfiable by a caller that does not control [m] at tp
     -- syscall()'s dispatch reaches this niladic function with whatever the
     table walk left in the register file, and could never supply it.  The
     premise was dead in the proof as well ([ProofSysUptime.v] introduced it
     and never used it), which is what let it survive.  [SpecYield.v] deleted
     its own copy for the same reason. *)
  (* acquire's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (14 <= av)%nat ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "time"'s -- sys_uptime acquires and releases [tickslock] in the same
     call, so this contract is BALANCED and [lks] is unchanged end to end. *)
  locks_below lks "time" ->
  sie_cap_gpr KT1 m av b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ pc_is pcE -∗
  is_tickslock γl -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mf : regfile) (t : mword 32),
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = zero_extend' 64 t ⌝ -∗
      sie_cap_gpr KT1 mf av b p -∗
      cpu_own n eb p b lks -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSUPTIME.
  Parameter wp_sys_uptime_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (γl : gname)
      (m : regfile) (n : nat) (eb : bool) (p : mword 64) (av : nat) (b : bool) (lks : gset string),
      wp_sys_uptime_sconf_body γl m n eb p av b lks.
End SYSUPTIME.

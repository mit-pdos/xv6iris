(* SpecPlicComplete.v -- the public interface of plic_complete.
   [plic_complete] (xv6-riscv/kernel/plic.c) tells the PLIC that this hart has
   finished serving the interrupt whose id it is handed:

     0x800054ec <plic_complete>:
       ...prologue (32-byte frame: ra, s0, s1)...
       mv     s1,a0            save the irq argument
       jal    cpuid            a0 = hart id
       slliw  a5,a0,0xd
       lui    a4,0xc201
       add    a5,a5,a4         a5 = PLIC + 0x201000 + hart*0x2000
       sw     s1,4(a5)         *PLIC_SCLAIM(hart) = irq
       ...epilogue...

   Like plicinithart, this runs on every hart concurrently, so it takes the
   device invariant [dev_inv] (WpUart.v) rather than owning [plic_frag], and
   each store opens it -- see SpecPlicinithart.v for why.

   AS FAR AS THE KERNEL'S PLIC PLAN GOES, plic_complete IS A NO-OP: the model's
   completion write only clears a [p_claimed] bit, and [plic_ok] (PlicPlan.v)
   constrains only the per-hart enable words.  So there is nothing to say about
   the PLIC on either side of the call, and correspondingly no constraint on
   the irq argument: the model's sclaim write is total, an out-of-range id
   simply completes nothing.  What the spec still earns is that the store
   ADDRESS decodes to this hart's real claim/complete register, which is what
   pins the precondition [bv_unsigned tp < dev_ncpu].

   Requires only the definitional layer + SpecCpuid -- never a whole-function
   proof file. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile InstrBytes HartTp.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import DevModel DiskPtsto WpUart.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


(* INTERRUPTS MUST BE DISABLED.  plic_complete's second instruction is an
   unbracketed [jal cpuid] (after [c.mv s1,a0] merely saves the argument) --
   there is no push_off/pop_off anywhere in its body -- and [cpuid]'s own
   contract (SpecCpuid.v) is [b = false]-ONLY (it reads [tp] mid-body; see the
   porting guide, "A function that READS tp mid-body must be stated at b =
   false"). A caller-supplied [b] cannot meet that precondition, so
   plic_complete itself can only be called with interrupts already off. This
   holds transitively at every real call site: plic_complete runs from
   devintr(), reached only from {user,kernel}trap() before interrupts are
   turned back on (usertrap's [intr_on()] sits in the syscall arm, never the
   device-interrupt arm; kerneltrap() PANICS if interrupts are found enabled,
   "kerneltrap: interrupts enabled") -- see
   claude-notes/projects/explicit-cpuid-porting-guide.md. So the contract is
   stated at the literal index [false] rather than a generic [b], with no
   [wp_next] wrapper (it would collapse via [wp_next_off] anyway, since the
   hart cannot move). *)
Definition wp_plic_complete_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (γd : uart_names) (γv : disk_names) (m0 : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let pcE := mword_of_int KernelSyms.plic_complete in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  bv_unsigned (rget m0 tp_idx) < Z.of_nat dev_ncpu ->
  (* plic_complete's own max depth: its 32-byte frame (4 slots) plus the two
     slots cpuid's frame needs below it. *)
  (6 <= n)%nat ->
  sie_cap_gpr KT1 m0 n false p -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  ( ∀ m' : regfile,
    sie_cap_gpr KT1 m' n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PLIC_COMPLETE.
  Parameter wp_plic_complete_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names) (m0 : regfile) (n : nat) (p : mword 64),
      wp_plic_complete_sconf_body γd γv m0 n p.
End PLIC_COMPLETE.

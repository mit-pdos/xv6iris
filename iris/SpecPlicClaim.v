(* SpecPlicClaim.v -- the public interface of plic_claim.
   [plic_claim] (xv6-riscv/kernel/plic.c) asks the PLIC which interrupt this
   hart should serve, and returns its source id (0 = nothing to serve):

     0x800054cc <plic_claim>:
       ...prologue...
       jal    cpuid            a0 = hart id
       slliw  a0,a0,0xd
       lui    a5,0xc201
       add    a5,a5,a0         a5 = PLIC + 0x201000 + hart*0x2000
       lw     a0,4(a5)         a0 = *PLIC_SCLAIM(hart)
       ...epilogue...

   Like plicinithart this runs on every hart concurrently, so it takes the
   device invariant [dev_inv] (WpUart.v) rather than owning [plic_frag] -- see
   SpecPlicinithart.v for why.  The claim READ is a state-changing MMIO
   transaction (the model clears the source's pending bit and marks it claimed),
   so it too is done with the invariant open; the mutation touches no enable
   word, so the kernel's plan [plic_ok] (PlicPlan.v) survives it.

   THE RETURN VALUE IS THE POINT.  A claim hands back the id of the source it
   took, and the plan says a hart's context can only ever have the machine's own
   two sources enabled -- so the id is 0, [uart_irq_id] or [virtio_irq_id], and
   nothing else ([plic_claim_ret_ok]).  That is exactly what makes devintr()'s
   three-way branch on the result exhaustive, and it is the one fact the loose
   shared invariant is strong enough to deliver.

   The returned word is the 32-bit register value sign-extended into a0 by
   [lw]; all three admissible ids are small and positive, so the post states
   them as the concrete 64-bit words 0, 10 and 1.

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
Import Defs.


(* the ids a claim can return, as the 64-bit words [lw] leaves in a0 *)
Definition plic_claim_a0_ok (v : mword 64) : Prop :=
  v = (mword_of_int 0 : mword 64) \/
  v = (mword_of_int (Z.of_N uart_irq_id) : mword 64) \/
  v = (mword_of_int (Z.of_N virtio_irq_id) : mword 64).

(* INTERRUPTS MUST BE DISABLED.  plic_claim's very first instruction is an
   unbracketed [jal cpuid] -- there is no push_off/pop_off anywhere in its
   body -- and [cpuid]'s own contract (SpecCpuid.v) is [b = false]-ONLY (it
   reads [tp] mid-body; see the porting guide, "A function that READS tp
   mid-body must be stated at b = false").  A caller-supplied [b] cannot meet
   that precondition, so plic_claim itself can only be called with interrupts
   already off.  This holds transitively at every real call site: plic_claim
   runs from devintr(), reached only from {user,kernel}trap() before
   interrupts are turned back on (usertrap's [intr_on()] sits in the syscall
   arm, never the device-interrupt arm; kerneltrap() PANICS if interrupts are
   found enabled, "kerneltrap: interrupts enabled") -- see
   claude-notes/projects/explicit-cpuid-porting-guide.md. So the contract is
   stated at the literal index [false] rather than a generic [b], with no
   [wp_next] wrapper (it would collapse via [wp_next_off] anyway, since the
   hart cannot move). *)
Definition wp_plic_claim_sconf_body `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γd : uart_names) (γv : disk_names)
    (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.plic_claim in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  bv_unsigned (rget m0 tp_idx) < Z.of_nat dev_ncpu ->
  (* plic_claim's own max depth: its 16-byte frame (2 slots) plus the two
     slots cpuid's frame needs below it. *)
  (4 <= n)%nat ->
  sie_cap_gpr m0 n false p -∗
  kernel_text -∗ pc_is pcE -∗
  dev_inv γd γv -∗
  ( ∀ m' : regfile,
    sie_cap_gpr m' n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\ m' !!! Regidx ra_idx = ra0 /\
      plic_claim_a0_ok (m' !!! Regidx a0_idx) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PLIC_CLAIM.
  Parameter wp_plic_claim_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γd : uart_names) (γv : disk_names)
      (Φ : mval -> iProp Σ) (m0 : regfile) (n : nat) (p : mword 64),
      wp_plic_claim_sconf_body γd γv Φ m0 n p.
End PLIC_CLAIM.

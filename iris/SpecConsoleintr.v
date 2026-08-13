(* SpecConsoleintr.v -- the public interface of consoleintr, stated
   independently of its proof.

     void consoleintr(int c);

   consoleintr is xv6's console line-discipline: it takes cons.lock, edits the
   input line (kill-line, backspace, echo through consputc), stores the byte
   in cons.buf, wakes a blocked consoleread() when a whole line has arrived,
   and releases cons.lock.  @ KernelSyms.consoleintr = 0x800002bc.

   *** THIS CONTRACT IS ASSUMED (LinkConsoleintr.v). ***  consoleintr is the
   one callee of uartintr with no proof, and this is the shape uartintr needs:
   a well-behaved kernel function that takes the running-thread bundle
   ([procs_inv] + [panic_wp], for the [wakeup] it performs) and gives back
   every callee-saved register, the interrupt-nesting level it was entered at,
   and the register file's totality.  It is stated in exactly [wakeup]'s shape
   because that is consoleintr's deepest sub-call.

   WHAT THE ASSUMPTION HIDES, and why it is worth naming: the echo path
   ([consputc], hence [uartputc_sync]) really does touch the UART, so a proven
   consoleintr could NOT have a contract silent about the transmitter -- it
   would need the transmitter token, which uartintr has just given back with
   tx_lock.  In the C that is a genuine race (uartputc_sync deliberately does
   not take tx_lock), and it is the same seam recorded in
   claude-notes/projects/uartwrite.md.  So this assumption is not merely
   "consoleintr is unproven": it also asserts that the echo is invisible to
   uartintr's caller, which is true of the register/lock state but not of the
   device.  Proving consoleintr will have to face that; nothing else in the
   uartintr proof depends on it. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import SmodeCore.
Require Import FdSlots.
Require Import ProcGeom.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import PanicStub.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import HartTp WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
From Kernel Require KernelSyms.

(* consoleintr's own frame (48 bytes = 6 slots) plus its deepest callee
   (wakeup, 18) is 24; this is that with slack, and the slack is deliberate --
   the contract is ASSUMED, so an over-approximation is the safe direction and
   uartintr is already stated against it.  consputc (16) and the two lock
   calls are all shallower than wakeup. *)
Definition consoleintr_stack : nat := 32%nat.

Definition wp_consoleintr_sconf_body `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
     (m : regfile) (γs : list gname)
    (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (consoleintr_stack <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  eq_vec (zero_reg : mword 64) (mycpu_ret (rget m (mword_of_int 4 : mword 5))) = false ->
  (* cons.lock's and wakeup's transient noff increments stay in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.consoleintr) -∗
  panic_wp_any -∗ procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
  ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr Mf K b pme -∗
      cpu_own lvl eb pme C b -∗
      kernel_text -∗ pc_is rettgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEINTR.
  Parameter wp_consoleintr_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
       (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_consoleintr_sconf_body m γs pme lvl K eb C b.
End CONSOLEINTR.

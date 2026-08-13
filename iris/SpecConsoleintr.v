(* SpecConsoleintr.v -- the public interface of consoleintr, stated
   independently of its proof.

     void consoleintr(int c);

   consoleintr is xv6's console line-discipline: it takes cons.lock, edits the
   input line (kill-line, backspace, echo through consputc), stores the byte
   in cons.buf, wakes a blocked consoleread() when a whole line has arrived,
   and releases cons.lock.  @ KernelSyms.consoleintr = 0x800002bc.

   ---- THE CREDENTIAL, AND WHY IT IS ONE EXISTENTIAL BUNDLE -------------

   This contract used to be ASSUMED, and what the assumption hid was the
   ECHO: [consputc] reaches [uartputc_sync], which really does take tx_lock
   and write the THR, so a contract silent about the transmitter was
   asserting something false about the device.  A proof cannot be silent
   about it, so consoleintr asks for exactly what its four callees ask for:

     acquire / release   [ConsoleInv.is_conslock]
     consputc            [WpUart.dev_inv] ∗ [UartTxInv.is_txlock] ∗ a
                         [UartTxInv.uart_sent_sub] to extend
     wakeup              [procs_inv] ∗ [panic_wp_any]

   ALL OF THEM ARE PERSISTENT, which is what makes the ripple cheap: the two
   lock credentials and the trace baseline are bundled here as
   [console_caps], with the two ghost NAMES existentially quantified, so a
   caller threading it gains a conjunct and NO new parameter.  uartintr's
   contract gains [console_caps], [SpecDevintr.devintr_caps] gains it, and
   the eight files that merely pass that bundle along do not change at all.

   [uart_sent_sub γu []] rather than a threaded [bs]: consoleintr's echo is
   of no interest to any caller, so there is nothing to thread -- the empty
   claim is the baseline each [consputc] call extends and then discards.
   Keeping it INSIDE the bundle rather than minting it from [dev_inv] is
   deliberate: minting costs a fupd that opens the device invariant, and the
   boot assembly that will eventually build this bundle has the real
   [uart_sent] in hand anyway (consoleinit hands it back).

   *** THE CONTRACT BELOW HAS NOT YET GROWN THE BUNDLE. ***  It is still the
   ASSUMED shape uartintr was written against; [console_caps] is defined here
   because ProofConsoleintr.v's blocks already consume it, and moving it into
   the contract is a one-conjunct change to [SpecDevintr.devintr_caps] that
   waits on the whole-function proof landing.

   WHAT IS OWED FOR IT: nothing constructs [console_caps] yet.  Both halves
   are [WpLock.newlock]s whose raw material exists and whose consumer did
   not -- [is_txlock] over [UartTxInv.tx_res] (ProofMain.v names the three
   pieces: [Hlkfresh], [Htx], [Hdoff]) and [is_conslock] over
   [ConsoleInv.cons_res], which additionally needs the ring's .bss cells in
   [SpecMain]'s boot bundle.  Until that lands the bundle is a premise of
   main; see claude-notes/projects/console.md. *)
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
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import ConsoleInv.
From Kernel Require KernelSyms.

(* consoleintr's own frame (48 bytes = 6 slots) plus its deepest callee
   (wakeup, 18) is 24; this is that with slack.  consputc (16) and the two
   lock calls (10) are all shallower than wakeup. *)
Definition consoleintr_stack : nat := 32%nat.

Section ConsoleCaps.
  Context `{!riscvGS Σ, !lockG Σ} `{!uartGhostG Σ}.

  (* The two locks the console's interrupt path takes, plus the trace
     baseline its echo extends.  The ghost NAMES are existential: nothing
     above consoleintr names either lock, so binding them here keeps the
     bundle parameter-free in [γu] alone. *)
  Definition console_caps (γu : uart_names) : iProp Σ :=
    (∃ γtx γc : gname,
       is_txlock γtx γu ∗ is_conslock γc ∗ uart_sent_sub γu [])%I.

  Global Instance console_caps_persistent γu : Persistent (console_caps γu).
  Proof. rewrite /console_caps. apply _. Qed.

End ConsoleCaps.

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

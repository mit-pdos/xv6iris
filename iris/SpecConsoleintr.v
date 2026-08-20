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
     wakeup              [procs_inv]

   ALL OF THEM ARE PERSISTENT, which is what makes the ripple cheap: the two
   lock credentials and the trace baseline are bundled here as
   [console_caps], with the two ghost NAMES existentially quantified, so a
   caller threading it gains a conjunct and NO new parameter.  uartintr's
   contract gains [console_caps], [SpecDevintr.devintr_caps] gains it, and
   every file that merely passes that bundle along changes by one name.

   [uart_sent_sub γu []] rather than a threaded [bs]: consoleintr's echo is
   of no interest to any caller, so there is nothing to thread -- the empty
   claim is the baseline each [consputc] call extends and then discards.
   Keeping it INSIDE the bundle rather than minting it from [dev_inv] is
   deliberate: minting costs a fupd that opens the device invariant, and the
   boot assembly that builds this bundle has the real [uart_sent] in hand
   anyway (consoleinit hands it back).

   [dev_inv] stays OUTSIDE the bundle: uartintr already holds it (its rx poll
   reads the device), so folding it in would make the caller's own hypothesis
   unreachable behind an existential pair of ghost names it does not know.

   WHERE IT COMES FROM: [ProofMain.mn_grp_printk], right after the
   consoleinit call that initializes both locks.  Both halves are
   [WpLock.newlock]s -- [is_txlock] over [UartTxInv.tx_res] (out of
   consoleinit's [lk_fresh] for tx_lock plus the transmitter token, both of
   which that block already held) and [is_conslock] over
   [ConsoleInv.cons_res] (out of consoleinit's own postcondition plus the
   ring's .bss cells, now a conjunct of [SpecMain.main_globals_raw]).  It
   then rides the [started] deposit to the secondaries.  Nothing is assumed;
   see claude-notes/projects/console.md.

   ---- WHAT THE CONTRACT NO LONGER ASKS ---------------------------------

   Two premises of the ASSUMED shape were vacuous and are gone: the register
   file's totality ([RegFile.rf_to_gmap_dom] proves it for every [m], with no
   hypothesis) and the non-null [mycpu_ret] of the entry [tp] -- nothing
   below consoleintr reads either.  Both were supplied at uartintr's call
   site by an [ltac:] that named the lemma; that is the tell. *)
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
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DiskPtsto WpUart.
Require Import UartTxInv.
Require Import ConsoleInv.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

(* consoleintr's own frame (48 bytes = 6 slots) plus its deepest callee
   (wakeup, 18) is 24; this is that with slack.  consputc (16) and the two
   lock calls (10) are all shallower than wakeup. *)
Notation consoleintr_stack := (32%nat) (only parsing).
Section ConsoleCaps.
  Context `{!riscvGS Σ, !xv6G Σ}.

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

Definition wp_consoleintr_sconf_body `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
     (γu : uart_names) (γv : disk_names) (m : regfile) (γs : list gname)
    (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string) :=
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (consoleintr_stack <= K)%nat ->
  length γs = NPROC ->
  (* cons.lock's and wakeup's transient noff increments stay in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (* acquire's order premise: every lock this hart already holds ranks below
     "cons"'s -- consoleintr acquires and releases cons.lock in the same
     call (BALANCED), so this contract is threaded on [lks] unchanged end to
     end.  "cons" (5) is also the LOWEST rank this call tree touches while
     the lock is held: [wakeup] (-> "proc", 11) surfaces its own
     [locks_below] premise, which the proof discharges from this one via
     [locks_below_mono]/[locks_below_union_singleton].  [consputc]'s public
     contract (SpecConsputc.v) does not surface an order premise at all --
     see the proof file's report for why that is not this function's
     obligation to supply. *)
  locks_below lks "cons" ->
  sie_cap_gpr KT1 m K b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.consoleintr) -∗
 procs_inv γs -∗
  dev_inv γu γv -∗
  console_caps γu -∗
  wp_next b pme (fun (CID : CpuId) =>
  ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr KT1 Mf K b pme -∗
      cpu_own lvl eb pme b lks -∗
      kernel_text -∗ pc_is rettgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type CONSOLEINTR.
  Parameter wp_consoleintr_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ} `{GEN : GenId} `{CID : CpuId}
       (γu : uart_names) (γv : disk_names) (m : regfile) (γs : list gname)
      (pme : mword 64) (lvl K : nat) (eb : bool) (b : bool) (lks : gset string),
      wp_consoleintr_sconf_body γu γv m γs pme lvl K eb b lks.
End CONSOLEINTR.

(* SpecPrintint.v -- the public interface of Printint, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     static void printint(long long xx, int base, int sign) {
       char buf[20]; int i; unsigned long long x;
       if (sign && (sign = (xx < 0))) x = -xx; else x = xx;
       i = 0;
       do { buf[i++] = digits[x % base]; } while ((x /= base) != 0);
       if (sign) buf[i++] = '-';
       while (--i >= 0) prputc(buf[i]);
     }

   THE POST SAYS NOTHING AT ALL ABOUT THE OUTPUT, and at XV6_REV 163d39b that
   is not a weakening for convenience but the ruling.  printint's character
   sink is [prputc] now, not [consputc]: the digits go to the SECOND 16550,
   whose wire nothing in the system tracks (claude-notes/projects/
   xv6-bump-163d39b.md, "THE OWNER'S RULING: UART1's output is
   unconstrained"), so there is no trace to extend and no [bs] to thread.
   What used to be here -- [UartTxInv.uart_sent_sub γd bs] in, [bs ++ cs] out
   -- was already existential in [cs] for a separate reason (a digit-accurate
   post would have to name the base-[base] representation of [xx] and thread
   it up through printk's format recursion, for no consumer); the ruling
   removes even the existential.

   THE ONE PRECONDITION THAT IS NOT BOILERPLATE is the range of [base]:

       10 <= uint base <= 16

   and both ends are load-bearing, not defensive:

   - the UPPER bound is what makes [digits[x % base]] a legal read.  [digits] is
     a 16-byte table, and the code indexes it by [x % base] with no check; a
     [base] above 16 would index off the end.
   - the LOWER bound is what makes [buf] big enough.  The do-while writes one
     byte per base-[base] digit of [x] and [buf] holds 20; a 64-bit [x] has at
     most 20 digits once [base >= 10], and in the negative case at most 19 plus
     the '-'.  With [base = 2] the same code would write 64 bytes and run off
     the frame, so this is a genuine caller obligation, and printk (which calls
     only with 10 and 16) discharges it.

   [kernel_data] supplies the [digits] table itself.

   THE PANIC PATH IS GONE, and with it everything this contract used to carry
   because of it: printk.c's [panicking]/[panicked] globals are deleted, so
   there are no flag cells and no [eq_vec]/[neq_vec] refutation premises.  What
   arrives in their place is what every printed byte costs -- a [tx_lock]
   acquire/release round trip per byte, at the SECOND port's lock -- so
   printint threads the ordinary spinlock-caller accounting ([cpu_own]
   net-zero, the [noff] transient bound) and brings ONE persistent credential,
   [SpecPrputc.prputc_env]: the second port's invariant, its transmit lock and
   the .data word its MMIO base is loaded from, with the ghost names
   existentially bound.  The transmitter token itself is never threaded -- it
   lives under that lock. *)
From Stdlib Require Import ZArith Bool Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import KernelText KernelDataInv.
Require Import RegFile WpNext.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import LockRank.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import SpecPrputc.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* printint's own frame is 8 slots ([c.addi16sp sp,-64] at +0x00), over
   [SpecPrputc.prputc_stack] = 20.  It was 24 over consputc's 16: the frame
   did not move at this bump, but uartputc_sync's did (32 -> 64 bytes), and
   that +4 arrives here through prputc. *)
Notation printint_stack := (28%nat) (only parsing).
Definition wp_printint_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (m0 : regfile) (K : nat)
    (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let pcE := mword_of_int KernelSyms.printint in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (printint_stack <= K)%nat ->
  (10 <= uint (m0 !!! Regidx a1_idx) <= 16)%Z ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* printint -> prputc -> uartputc_sync, at the SECOND port's lock
     ([LockRank.v]: "uart" was re-keyed to "uart0"/"uart1" at this bump) *)
  locks_below lks "uart1" ->
  sie_cap_gpr kt m0 K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  prputc_env -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf,
    sie_cap_gpr kt mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PRINTINT.
  Parameter wp_printint_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (m0 : regfile) (K : nat)
      (n : nat) (eb : bool) (b : bool) (p : mword 64) (lks : gset string),
      wp_printint_sconf_body kt m0 K n eb b p lks.
End PRINTINT.

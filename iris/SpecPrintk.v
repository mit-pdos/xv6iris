(* SpecPrintk.v -- the public interface of Printk, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     int printk(char *fmt, ...);

   THE POST.  printk promises that SOME byte list [cs] was appended to what this
   caller has provably sent, and returns 0.  It does NOT say which bytes:
   nothing in the kernel reads back what was printed, and a byte-accurate post
   would have to carry a decimal/hex rendering of every vararg up through the
   format recursion -- for no consumer.

   THERE IS ONLY ONE PATH NOW.  printk.c's two [volatile int] globals are
   deleted:

       -volatile int panicking = 0;
       -volatile int panicked  = 0;
        printk(...) { -if (panicking == 0) acquire(&pr.lock);  +acquire(&pr.lock); ... }

   so printk ALWAYS takes [pr.lock], and the whole panic-path story this file
   used to tell -- "printk then takes NO pr.lock, and uartputc_sync does no
   push_off/pop_off, which is why no lock resource and no [intr_count] appear
   here" -- describes code that no longer exists.  Three things follow.

   (a) THE FLAG CELLS ARE GONE.  No [panicking]/[panicked] points-to premises,
       no postcondition copies of them, and no [eq_vec]/[neq_vec] refutation
       premises selecting the path.

   (b) THE LOCKS ARRIVE.  Two of them, and both are persistent credentials
       rather than resources: [pr.lock] itself, which after the transmitter
       moved out of it protects NOTHING ([SpecPrintkGen.pr_res] is [emp] -- see
       (c)), and [UartTxInv.is_txlock γl γd], which every byte below needs.
       With them comes the ordinary spinlock-caller accounting: [cpu_own]
       threaded net-zero (printk leaves the interrupt level as it found it),
       [panic_wp_any] for acquire's "already holding" arm, and a transient
       bound on [noff] -- [+2] here, not [+1], because printk holds pr.lock
       while the cone below takes tx_lock.

   (c) THE TRANSMITTER IS NOT THREADED, and the trace claim WEAKENS.
       [uart_tx_own] is [tx_lock]'s resource now, so it is neither a premise
       nor a postcondition.  And since that lock is re-acquired PER BYTE,
       another hart can interleave between two of printk's bytes: a CONTIGUOUS
       [uart_sent γd (l ++ bs)] would be false.  The honest claim is the
       sublist [UartTxInv.uart_sent_sub], threaded [bs] in / [bs ++ cs] out.
       Threading it IN is what makes the empty-format path work (a printk whose
       format string is empty prints nothing and must still return something),
       and costs nothing: [uart_sent_sub] is persistent.

   THE REST OF THE PRECONDITION is unchanged, and it has exactly three parts
   beyond the usual capability/config boilerplate.

   1. THE FORMAT STRING is a real C string: [fmt ↦ₛ{dqf} f] with [nonul f].  It
      is handed back untouched -- printk only reads it.

   2. THE VARARGS.  A variadic call has no types at the call site, so the caller
      DESCRIBES its arguments: [descs] says, for each vararg in order, whether it
      is an integer-ish value ([PkANum] -- %d/%u/%x/%p/%c and the long forms), a
      null [char *] ([PkANull], which printk prints as "(null)"), or a [char *]
      to a string it owns ([PkAStr dq s]).  The description must MATCH the
      format string --

          pk_kinds f = map pk_desc_kind descs

      -- which is the honest statement of C's unchecked contract: a "%s" whose
      argument is not a string is undefined behaviour, and here it is simply
      unprovable.  The [PkAStr] resources are handed back with the same
      fractions.

      The varargs themselves are not extra parameters: the ABI puts them in
      a1..a7, so vararg [j] IS [m0 !!! a(j+1)] ([pk_vararg]).

   3. AT MOST SEVEN VARARGS.  printk spills a1..a7 into its own frame and walks
      [ap] up through them; an eighth [va_arg] would read the CALLER's frame,
      which printk does not own.  So [length descs <= 7] is a genuine caller
      obligation -- and one every call site in xv6 meets with room to spare. *)
From Stdlib Require Import ZArith Bool Lia List String Ascii.
From stdpp Require Import gmap list bitvector.definitions.
From iris.algebra Require Import dfrac.
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
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Import SpecPanic.
Require Import PrintkFmt.
From Kernel Require KernelSyms.


(* ---------------------------------------------------------------------- *)
(* The caller's description of one vararg (see (2) above).                 *)
(* ---------------------------------------------------------------------- *)
Inductive pk_arg_desc :=
  | PkANum                                (* an integer/char/pointer value *)
  | PkANull                               (* a null char* -- printed "(null)" *)
  | PkAStr (dq : dfrac) (s : string).     (* a char* to [s], owned at [dq] *)

Definition pk_desc_kind (d : pk_arg_desc) : pk_kind :=
  match d with
  | PkANum => PkNum
  | PkANull => PkStr
  | PkAStr _ _ => PkStr
  end.

Definition pk_desc_res `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} (v : mword 64) (d : pk_arg_desc) : iProp Σ :=
  match d with
  | PkANum => True
  | PkANull => ⌜v = zero_reg⌝
  (* a [char *] to a real string is NOT null -- the caller has to say so.
     [v ↦ₛ{dq} s] alone does not imply it: nothing in the points-to rules out
     address 0, and the arm needs the [beqz] at 0x21e to fall through. *)
  | PkAStr dq s => ⌜nonul s = true⌝ ∗ ⌜eq_vec v zero_reg = false⌝ ∗ v ↦ₛ{dq} s
  end.

(* Vararg [j] is the entry value of a(j+1) = x(11+j): the ABI passes the first
   seven in registers, and printk's prologue spills them into its own frame. *)
Definition pk_vararg (m : regfile) (j : nat) : mword 64 :=
  m !!! Regidx (mword_of_int (11 + Z.of_nat j) : mword 5).

(* [static struct { struct spinlock lock; } pr;] -- the lock is the FIRST
   field, so the object's address IS the lock's.  Spelled here rather than
   taken from SpecPrintkGen.v, which sits ABOVE this file and reuses this
   file's vocabulary; [SpecPrintkGen.pr_lock] is the same address and
   [SpecPrintkGen.pr_res] the same (empty) resource, so the two [is_lock]s are
   the same proposition. *)
Definition pk_pr_lock : mword 64 := mword_of_int KernelSyms.pr.

(* printk's own frame is 24 slots ([addi sp,sp,-192] at 0x8000050a), over
   printint's 24. *)
Definition printk_stack : nat := 48%nat.

Definition wp_printk_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr : gname) (γl : gname) (γd : uart_names) (γv : disk_names)
    (m0 : regfile) (K : nat) (bs : list (bv 8))
    (n : nat) (eb : bool) (C : iProp Σ) (dqf : dfrac)
    (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.printk in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let fmt := m0 !!! Regidx a0_idx in
  (printk_stack <= K)%nat ->
  (* printk's index [i] is a C [int], and the code computes [i + 1 .. i + 3]
     with [addiw]; past 2^31 those wrap.  Not derivable from the points-to
     (fractional bytes may alias), so it is a caller obligation -- met by
     every real format string by ~nine orders of magnitude. *)
  (Z.of_nat (String.length f) < 2147483645)%Z ->
  nonul f = true ->
  pk_kinds f = map pk_desc_kind descs ->
  (length descs <= 7)%nat ->
  (* TWO nested acquires -- pr.lock, then tx_lock per byte underneath it -- so
     the [noff] headroom the callees want is [n + 2], not [n + 1]. *)
  (Z.of_nat n + 2 < 2 ^ 31)%Z ->
  sie_cap_gpr m0 K b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  (* pr.lock protects nothing at all now: the transmitter it used to own moved
     to tx_lock, which is where the two transmit paths meet.  What is left is
     mutual exclusion between two harts' format walks -- real, but invisible in
     separation logic, so the resource is [emp] and the acquire is nearly
     free. *)
  is_lock γpr pk_pr_lock "pr"%string (emp : iProp Σ) -∗
  dev_inv γd γv -∗
  is_txlock γl γd -∗
  uart_sent_sub γd bs -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf cs,
    sie_cap_gpr mf K b p -∗
    cpu_own n eb p C b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0
      /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    uart_sent_sub γd (bs ++ cs) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PRINTK.
  Parameter wp_printk_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γl : gname) (γd : uart_names) (γv : disk_names)
      (m0 : regfile) (K : nat) (bs : list (bv 8))
      (n : nat) (eb : bool) (C : iProp Σ) {dqf : dfrac}
      (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64),
      wp_printk_sconf_body γpr γl γd γv m0 K bs n eb C dqf f descs b p.
End PRINTK.

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
       moved out of it protects NOTHING ([pr_res] below is [emp] -- see
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
Require Import PanicStub.
Require Export PrintkArgs.
From Kernel Require KernelSyms.


(* [pk_arg_desc] / [pk_desc_kind] / [pk_desc_res] / [pk_vararg] / [pk_pr_lock]
   are the CALLER's vocabulary and live in PrintkArgs.v, which this file
   [Require Export]s -- panic's spec needs them while sitting below this one.
   Nothing that reached them through SpecPrintk.v has to change. *)

(* printk's own frame is 24 slots ([addi sp,sp,-192] at 0x8000050a), over
   printint's 24. *)
Definition printk_stack : nat := 48%nat.

Definition wp_printk_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr : gname) (γl : gname) (γd : uart_names) (γv : disk_names)
    (m0 : regfile) (K : nat) (bs : list (bv 8))
    (n : nat) (eb : bool) (C : iProp Σ) (dqf : dfrac)
    (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64) (lks : gset nat) :=
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
  (* acquire's order premise, at the LOWEST rank this function (or a callee)
     acquires: "pr" (rank 14) is outermost, and the inner per-byte "uart"
     acquire (rank 15 > 14) follows from this by
     [LockRank.locks_below_union_singleton]. *)
  locks_below lks (lock_rank "pr") ->
  sie_cap_gpr m0 K b p -∗
  cpu_own n eb p C b lks -∗
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
    cpu_own n eb p C b lks -∗
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
      (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64) (lks : gset nat),
      wp_printk_sconf_body γpr γl γd γv m0 K bs n eb C dqf f descs b p lks.
End PRINTK.

(* ========================================================================
   THE WEAK COROLLARY.  [wp_printk_sconf_body] above is the real, code-derived
   contract, and it is what ~15 non-trace callers (main's boot banners,
   usertrap's unexpected-scause diagnostic, and several fs.c error arms) do
   NOT want to carry in full: threading [γl]/[bs]/a general [n] and the
   [uart_sent_sub] trace postcondition through a whole proof cone just to
   call printk once, on a path nobody reads the output of, is pure overhead.

   [wp_printk_gen_sconf_body] is [wp_printk_sconf_body] with [n := 0] and
   [bs := []] baked in and the trace/return-value postcondition dropped --
   the strictly weaker fact those callers actually need.  [printk_env]
   bundles exactly the extra ingredients that instantiation wants
   ([γl]/[is_txlock] and the trivial [uart_sent_sub γd []] witness) as ONE
   persistent credential, and [printk_gen_contract] packages the whole thing
   as a [Prop] so a caller can carry it as a plain hypothesis instead of
   instantiating a functor -- [LinkPrintk.v] proves it once, as a corollary
   of [PRINTK] above, and every consumer threads that proof (or, for
   main/main-secondary/usertrap, the [PRINTK_GEN] functor it also seals). *)

(* the [pr] lock, the one object the general path touches that panic's own
   call site does not thread explicitly.  [static struct { struct spinlock
   lock; } pr;] -- the lock is the FIRST field, so the object's address IS
   the lock's.  Same address as [PrintkArgs.pk_pr_lock]. *)
Definition pr_lock : mword 64 := mword_of_int KernelSyms.pr.

Section PrintkGen.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* pr.lock protects NOTHING: d80e61c5 put uartputc_sync's THR write under
     [tx_lock], so the transmitter is [UartTxInv.tx_res]'s and pr.lock is left
     serializing format walks, which has no separation-logic content.  [emp]
     over [True] because it is the unit of [∗], so [newlock]'s resource
     argument is discharged by nothing at all. *)
  Definition pr_res (γd : uart_names) : iProp Σ := emp%I.

  (* The whole general-path credential, and it is PERSISTENT -- which is
     what lets it cross main's [started] invariant to the other harts for
     free (claude-notes/projects/main-boot.md). [is_txlock]/[uart_sent_sub]
     are what [wp_printk_sconf_body] additionally wants over [is_lock]/
     [dev_inv] -- both already sitting at this credential's one construction
     site (ProofMain.v's [mn_grp_printk], right where [console_caps] is built
     from the very same [Htxinv]/[Hdoff]/[Hsent]).  [uart_sent_sub γd []] is
     the trivial (any-trace) witness: gen callers make no claim about what
     has been sent, so the empty sublist is all the corollary below ever
     needs to hand [wp_printk_sconf_body]'s [bs]. *)
  Definition printk_env (γpr : gname) (γd : uart_names) (γv : disk_names) : iProp Σ :=
    (is_lock γpr pr_lock "pr"%string (pr_res γd) ∗
     uart_dlab_off γd ∗
     dev_inv γd γv ∗
     (∃ γl : gname, is_txlock γl γd) ∗
     uart_sent_sub γd [])%I.

  Global Instance printk_env_persistent γpr γd γv : Persistent (printk_env γpr γd γv).
  Proof. apply _. Qed.

End PrintkGen.

Definition wp_printk_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr : gname) (γd : uart_names) (γv : disk_names)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset nat) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE : mword 64 := mword_of_int KernelSyms.printk in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let fmt := m0 !!! Regidx a0_idx in
  (* a LITERAL, not [printk_stack <= K], so a caller's bare [ltac:(lia)]
     still closes it -- [printk_stack] is opaque to [lia] and every
     established call site just does [ltac:(lia)] against its own ambient
     bound.  Matches [printk_stack] exactly: same frame, minus [γl]/[bs]/[n]
     in this contract's own argument list. *)
  (48 <= K)%nat ->
  (Z.of_nat (String.length f) < 2147483645)%Z ->
  nonul f = true ->
  pk_kinds f = map pk_desc_kind descs ->
  (length descs <= 7)%nat ->
  (* acquire's order premise, at the LOWEST rank this function (or a callee)
     acquires: "pr" (rank 14), see [wp_printk_sconf_body]. *)
  locks_below lks (lock_rank "pr") ->
  sie_cap_gpr m0 K b pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp -∗
  (* the interrupt level is left exactly as found: acquire/release pair *)
  cpu_own 0%nat eb pj C b lks -∗
  (* the general path's whole credential (persistent) *)
  printk_env γpr γd γv -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
    sie_cap_gpr mf K b pj -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    cpu_own 0%nat eb pj C b lks -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* printk's general contract as a PROP, so a caller can carry it as a
   HYPOTHESIS rather than instantiate a functor -- the [Prop] twin of
   [SpecPanic.panic_wp_any], and the same idiom [ProofBmap.balloc_contract]
   uses.  [LinkPrintk.printk_gen_contract_holds] proves it unconditionally, so
   a holder pays nothing beyond the standing platform/stdlib axioms. *)
Definition printk_gen_contract `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId}
    (γpr : gname) (γd : uart_names) (γv : disk_names) : Prop :=
  forall (CIDp : CpuId)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset nat),
    wp_printk_gen_sconf_body (CID := CIDp) γpr γd γv m0 K eb pj C dqf f descs b lks.

Module Type PRINTK_GEN.
  Parameter wp_printk_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset nat),
      wp_printk_gen_sconf_body γpr γd γv m0 K eb pj C dqf f descs b lks.
End PRINTK_GEN.

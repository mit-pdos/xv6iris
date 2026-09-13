(* SpecPrintk.v -- the public interface of Printk, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

     int printk(char *fmt, ...);

   THE POST SAYS NOTHING ABOUT THE OUTPUT, and returns 0.  At XV6_REV 163d39b
   printk's character sink is [prputc] -- uartputc_sync at the SECOND 16550 --
   and nothing in the system tracks that wire (claude-notes/projects/
   xv6-bump-163d39b.md, "THE OWNER'S RULING: UART1's output is
   unconstrained").  So the trace claim this contract used to carry --
   [UartTxInv.uart_sent_sub γd bs] in, [bs ++ cs] out, with [cs] existential
   -- is gone in both directions, and with it the [γl]/[γd]/[γv]/[bs]
   parameters that existed only to state it.  What replaces the three console
   credentials is ONE: [SpecPrputc.prputc_env].

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
       (c)), and, inside [SpecPrputc.prputc_env], the SECOND port's tx_lock,
       which every byte below needs.  With them comes the ordinary
       spinlock-caller accounting: [cpu_own] threaded net-zero (printk leaves
       the interrupt level as it found it), and a transient bound on [noff] --
       [+2] here, not [+1], because printk holds pr.lock while the cone below
       takes that tx_lock.

   (c) THE TRANSMITTER IS NOT THREADED, AND NEITHER IS A TRACE.
       [uart_tx_own] is [tx_lock]'s resource, so it is neither a premise nor a
       postcondition.  And the trace claim is not weakened but ABSENT: the
       bytes go to UART1, whose wire is unconstrained by ruling, so there is
       nothing for printk to promise and nothing for a caller to accumulate.
       [SpecPrputc.v]'s header carries the ruling and the reasoning; the
       [uart_sent_sub] uartputc_sync still asks for is minted inside
       [ProofPrputc] out of nothing at all.

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
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpLock.
Require Import CpuOwn.
Require Import UartTxInv.
Require Export PrintkArgs.
Require Import SpecPrputc.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* [pk_arg_desc] / [pk_desc_kind] / [pk_desc_res] / [pk_vararg] / [pk_pr_lock]
   are the CALLER's vocabulary and live in PrintkArgs.v, which this file
   [Require Export]s -- panic's spec needs them while sitting below this one.
   Nothing that reached them through SpecPrintk.v has to change. *)

(* printk's own frame is 24 slots ([addi sp,sp,-192] at +0x00), over
   printint's [SpecPrintint.printint_stack] = 28.

   IT WENT 48 -> 52 AT 163d39b.  printk's own frame did not move (its shape
   did not change at all -- the bump was pure relayout for this function);
   uartputc_sync's did, 32 -> 64 bytes, and the +4 arrives here through
   prputc -> printint.  Every derived bound above -- [panic_stack], and the
   literal in [wp_printk_gen_sconf_body] below -- moved with it. *)
Notation printk_stack := (52%nat) (only parsing).
Definition wp_printk_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γpr : gname)
    (m0 : regfile) (K : nat)
    (n : nat) (eb : bool) (dqf : dfrac)
    (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64) (lks : gset string) :=
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
  locks_below lks "pr" ->
  sie_cap_gpr kt m0 K b p -∗
  cpu_own n eb p b lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  (* pr.lock protects nothing at all now: the transmitter it used to own moved
     to tx_lock, which is where the two transmit paths meet.  What is left is
     mutual exclusion between two harts' format walks -- real, but invisible in
     separation logic, so the resource is [emp] and the acquire is nearly
     free. *)
  is_lock γpr pk_pr_lock "pr"%string <{ emp : iProp Σ }> -∗
  (* THE SECOND PORT, AND NOTHING OF THE CONSOLE'S.  [SpecPrputc.v]. *)
  prputc_env -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf,
    sie_cap_gpr kt mf K b p -∗
    cpu_own n eb p b lks -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0
      /\ mf !!! Regidx a0_idx = zero_reg ⌝ -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type PRINTK.
  Parameter wp_printk_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γpr : gname)
      (m0 : regfile) (K : nat)
      (n : nat) (eb : bool) {dqf : dfrac}
      (f : string) (descs : list pk_arg_desc) (b : bool) (p : mword 64) (lks : gset string),
      wp_printk_sconf_body kt γpr m0 K n eb dqf f descs b p lks.
End PRINTK.

(* ========================================================================
   THE WEAK COROLLARY.  [wp_printk_sconf_body] above is the real, code-derived
   contract, and it is what ~15 non-trace callers (main's boot banners,
   usertrap's unexpected-scause diagnostic, and several fs.c error arms) do
   NOT want to carry in full: threading a general [n] and the return-value
   postcondition through a whole proof cone just to call printk once is pure
   overhead.  (Until 163d39b the gap was much wider -- [γl], [bs] and a trace
   postcondition too -- and it is worth noting that the ruling on the second
   port's wire has made the FULL contract nearly as cheap as this corollary.)

   [wp_printk_gen_sconf_body] is [wp_printk_sconf_body] with [n := 0] baked in
   and the return-value postcondition dropped -- the strictly weaker fact
   those callers actually need.  [printk_env] bundles the two persistent
   credentials that instantiation wants (pr.lock's [is_lock] and
   [SpecPrputc.prputc_env]) as ONE, and [printk_gen_contract] packages the
   whole thing as a [Prop] so a caller can carry it as a plain hypothesis
   instead of instantiating a functor -- [LinkPrintk.v] proves it once, as a
   corollary of [PRINTK] above, and every consumer threads that proof (or, for
   main/main-secondary/usertrap, the [PRINTK_GEN] functor it also seals).

   ITS ARGUMENT LIST DID NOT MOVE AT 163d39b, and that is deliberate: [γd] and
   [γv] survive as parameters of [printk_env] (and hence of this corollary)
   even though the credential no longer names the console's device bundle,
   because ~55 files thread them and a premise that is merely unused is still
   provable.  What changed is the DEFINITION of [printk_env], one file, no
   fan-out -- and the one construction site, [ProofMain.v]'s [mn_grp_printk],
   which now has to supply the second port instead of the console. *)

(* the [pr] lock, the one object the general path touches that panic's own
   call site does not thread explicitly.  [static struct { struct spinlock
   lock; } pr;] -- the lock is the FIRST field, so the object's address IS
   the lock's.  Same address as [PrintkArgs.pk_pr_lock]. *)
Definition pr_lock : mword 64 := mword_of_int KernelSyms.pr.

Section PrintkGen.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}.

  (* pr.lock protects NOTHING: d80e61c5 put uartputc_sync's THR write under
     [tx_lock], so the transmitter is [UartTxInv.tx_res]'s and pr.lock is left
     serializing format walks, which has no separation-logic content.  [emp]
     over [True] because it is the unit of [∗], so [newlock]'s resource
     argument is discharged by nothing at all. *)
  Definition pr_res (γd : uart_names) : iProp Σ := emp%I.

  (* The whole general-path credential, and it is PERSISTENT -- which is
     what lets it cross main's [started] invariant to the other harts for
     free (claude-notes/projects/main-boot.md).

     IT NAMES THE SECOND PORT NOW.  What used to be here was the console
     quadruple -- [uart_dlab_off γd], [dev_inv γd γv], an existential
     [is_txlock γl γd] and the trivial [uart_sent_sub γd []].  printk prints
     through [prputc] at XV6_REV 163d39b, so every one of those is the wrong
     port's, and [SpecPrputc.prputc_env] (UART1's invariant, UART1's tx lock
     with its frozen DLAB, and the .data word UART1's MMIO base is loaded
     from) is what the cone actually consumes.  The trace witness is not
     re-pointed but DROPPED: nothing tracks that wire, so nothing below asks
     for one.

     [γd]/[γv] STAY IN THE ARGUMENT LIST even though only [pr_res γd] still
     mentions one, and [pr_res] is [emp].  Keeping the arity is what makes
     this a one-file change: ~55 files name [printk_env γpr γd γv] and none
     of them moves. *)
  Definition printk_env (γpr : gname) (γd : uart_names) (γv : disk_names) : iProp Σ :=
    (is_lock γpr pr_lock "pr"%string <{ pr_res γd }> ∗
     prputc_env)%I.

  Global Instance printk_env_persistent γpr γd γv : Persistent (printk_env γpr γd γv).
  Proof. apply _. Qed.

  (* printk_env IS panic_env, with γpr concrete: pr.lock's resource is [emp]
     on both sides ([pr_res] is [emp]) and the address is the same
     [KernelSyms.pr] under two names, and the second conjunct is literally the
     same [prputc_env].  So any site already carrying the general printk
     credential can call panic without gaining a premise -- which is what
     makes the first conversions free, and what kept this derivation working
     across both the 06ea57f emptying and the 163d39b refill. *)
  Lemma printk_env_panic γpr γd γv :
    printk_env γpr γd γv -∗ SpecPanic.panic_env.
  Proof.
    iIntros "(#Hlk & #Hpre)".
    iApply (SpecPanic.panic_env_of γpr with "[] Hpre").
    rewrite /pr_res /pr_lock /PrintkArgs.pk_pr_lock. iExact "Hlk".
  Qed.

End PrintkGen.

Definition wp_printk_gen_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (kt : ktier) (γpr : gname) (γd : uart_names) (γv : disk_names)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset string) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE : mword 64 := mword_of_int KernelSyms.printk in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let fmt := m0 !!! Regidx a0_idx in
  (* a LITERAL, not [printk_stack <= K], so a caller's bare [ltac:(lia)]
     still closes it -- [printk_stack] is opaque to [lia] and every
     established call site just does [ltac:(lia)] against its own ambient
     bound.  Matches [printk_stack] exactly: same frame, minus [n] in this
     contract's own argument list.  IT WENT 48 -> 52 AT 163d39b (see
     [printk_stack]), so a caller whose own budget was exactly 48 slots deep
     here no longer closes. *)
  (52 <= K)%nat ->
  (Z.of_nat (String.length f) < 2147483645)%Z ->
  nonul f = true ->
  pk_kinds f = map pk_desc_kind descs ->
  (length descs <= 7)%nat ->
  (* acquire's order premise, at the LOWEST rank this function (or a callee)
     acquires: "pr" (rank 14), see [wp_printk_sconf_body]. *)
  locks_below lks "pr" ->
  sie_cap_gpr kt m0 K b pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  (* the interrupt level is left exactly as found: acquire/release pair *)
  cpu_own 0%nat eb pj b lks -∗
  (* the general path's whole credential (persistent) *)
  printk_env γpr γd γv -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
    sie_cap_gpr kt mf K b pj -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    cpu_own 0%nat eb pj b lks -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* printk's general contract as a PROP, so a caller can carry it as a
   HYPOTHESIS rather than instantiate a functor -- the [Prop] twin of
   [SpecPanic]'s own credentials, and the same idiom [ProofBmap.balloc_contract]
   uses.  [LinkPrintk.printk_gen_contract_holds] proves it unconditionally, so
   a holder pays nothing beyond the standing platform/stdlib axioms. *)
Definition printk_gen_contract `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId}
    {kt : ktier} (γpr : gname) (γd : uart_names) (γv : disk_names) : Prop :=
  forall (CIDp : CpuId) (XIp : CurCtx)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset string),
    wp_printk_gen_sconf_body kt (CID := CIDp) (XI := XIp) γpr γd γv m0 K eb pj dqf f descs b lks.

Module Type PRINTK_GEN.
  Parameter wp_printk_gen_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (kt : ktier) (γpr : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool) (lks : gset string),
      wp_printk_gen_sconf_body kt γpr γd γv m0 K eb pj dqf f descs b lks.
End PRINTK_GEN.

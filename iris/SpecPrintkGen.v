(* SpecPrintkGen.v -- printk's GENERAL-path interface, stated as an ASSUMED
   contract ([Module Type] here, [Axiom] in LinkPrintkGen.v -- the shape
   claude-notes/design/spec-modules.md calls "An ASSUMED callee").

     int printk(char *fmt, ...);

   WHY A SECOND INTERFACE.  [SpecPrintk.wp_printk_sconf] is PROVEN, but only on
   the PANIC path: it carries [eq_vec (sign_extend' 64 pv) zero_reg = false],
   i.e. [panicking <> 0], where printk takes no lock and uartputc_sync spins
   with interrupts as it finds them.  Every ordinary caller -- main()'s four
   calls among them -- runs the GENERAL path, which acquires [pr.lock] around
   the whole format walk.  That path is blocked on uartputc_sync's general
   contract (claude-notes/completed/printk.md), so it is assumed here and main's
   proof is a functor over it; proving it later replaces exactly the [Axiom].

   Everything about the format string and the varargs is UNCHANGED and reused
   from SpecPrintk.v ([pk_arg_desc], [pk_desc_res], [pk_vararg], [pk_kinds]) --
   the caller's obligations do not depend on which contract is used.

   *** THE TWO PATHS HAVE MERGED UPSTREAM (d80e61c5), and this file has not
   caught up. *** [panicking] and [panicked] are DELETED from printk.c, so
   printk always acquires pr.lock and uartputc_sync always acquires tx_lock:
   SpecPrintk.v now states that one path, lock accounting and all.  What is
   left here that SpecPrintk.v does not have is (a) the [Prop]-shaped
   [printk_gen_contract] / [PRINTK_GEN] packaging its ~15 consumers carry, and
   (b) a post that promises NOTHING about the trace, which is why those
   consumers need no [uart_sent_sub] threading.  Folding this file into
   SpecPrintk.v and retiring [LinkPrintkGen]'s [Axiom] is now a real
   possibility rather than a blocked one; it is a separate sweep.

   Two things consequently differ from what this header used to say:

   1. THERE ARE NO FLAGS.  [printk_flags_inv] -- the invariant that owned the
      two [volatile int] cells so no caller had to -- is DELETED with them.
      [printk_env] is three conjuncts now, not four.

   2. THE TRANSMITTER NO LONGER RIDES UNDER pr.lock.  It belongs to [tx_lock]
      ([UartTxInv.tx_res]), which uartputc_sync takes for itself, so [pr_res]
      collapses to [emp] -- see the comment on it below.

   What is unchanged: the general path TAKES A LOCK, so acquire's cone comes
   with it -- [cpu_own] threaded net-zero (printk leaves the interrupt level as
   it found it) plus the tp/cid convention, and [panic_wp] for acquire's
   "already holding" arm.  No [sched_vc]/[procs_inv]: printk never sleeps.

   Requires only the definitional layer plus SpecPrintk.v's vocabulary -- never
   a [Proof*] file. *)
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
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import DiskPtsto WpUart.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import PrintkFmt.
Require Import PanicStub.
Require Import SpecPrintk.
From Kernel Require KernelSyms.

(* the [pr] lock, the one object the general path touches that the panic path
   does not.  [static struct { struct spinlock lock; } pr;] -- the lock is the
   FIRST field, so the object's address IS the lock's. *)
Definition pr_lock : mword 64 := mword_of_int KernelSyms.pr.

Section SpecPrintkGen.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* What pr.lock protects: NOTHING.                                      *)
  (*                                                                      *)
  (* It used to be THE TRANSMITTER -- the exclusive [uart_tx_own] token    *)
  (* plus its [uart_sent] receipt -- because on the general path pr.lock   *)
  (* was the only thing serializing output, and uartputc_sync's contract   *)
  (* took the token from its caller.  Upstream d80e61c5 moved that:        *)
  (* uartputc_sync now takes [tx_lock] itself (a spinlock again), so the   *)
  (* transmitter is [UartTxInv.tx_res]'s and the two transmit paths        *)
  (* (uartputc_sync and uartwrite) meet in that lock rather than in the    *)
  (* caller.  pr.lock is left guarding no C data and no ghost resource:    *)
  (* what it still buys is that two harts' format walks do not interleave  *)
  (* mid-line, which is real but has no separation-logic content.  Hence   *)
  (* [emp] -- chosen over [True] because it is the unit of [∗], so         *)
  (* [newlock]'s resource argument is discharged by nothing at all and     *)
  (* release's give-back goal closes the same way; and it is what makes    *)
  (* printk's new UNCONDITIONAL [acquire(&pr.lock)] nearly free.           *)
  (*                                                                      *)
  (* [γd] is kept as a parameter although the body no longer mentions it,  *)
  (* so that [printk_env]'s arity and every caller's [is_lock γpr pr_lock  *)
  (* "pr" (pr_res γd)] read unchanged.                                     *)
  (* ------------------------------------------------------------------- *)
  Definition pr_res (γd : uart_names) : iProp Σ := emp%I.

  (* ------------------------------------------------------------------- *)
  (* The whole general-path credential, and it is PERSISTENT -- which is   *)
  (* what lets it cross main's [started] invariant to the other harts for  *)
  (* free (claude-notes/projects/main-boot.md).                            *)
  (* ------------------------------------------------------------------- *)
  Definition printk_env (γpr : gname) (γd : uart_names) (γv : disk_names) : iProp Σ :=
    (is_lock γpr pr_lock "pr"%string (pr_res γd) ∗
     uart_dlab_off γd ∗
     dev_inv γd γv)%I.

  Global Instance printk_env_persistent γpr γd γv : Persistent (printk_env γpr γd γv).
  Proof. apply _. Qed.

End SpecPrintkGen.

Definition wp_printk_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
    (γpr : gname) (γd : uart_names) (γv : disk_names)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE : mword 64 := mword_of_int KernelSyms.printk in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  let fmt := m0 !!! Regidx a0_idx in
  (* printk's own 24-slot frame, over printint's 14 *)
  (38 <= K)%nat ->
  (* printk's index [i] is a C [int], and the code computes [i + 1 .. i + 3]
     with [addiw]; past 2^31 those wrap. *)
  (Z.of_nat (String.length f) < 2147483645)%Z ->
  nonul f = true ->
  pk_kinds f = map pk_desc_kind descs ->
  (length descs <= 7)%nat ->
  sie_cap_gpr m0 K b pj -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp -∗
  (* the interrupt level is left exactly as found: acquire/release pair *)
  cpu_own 0%nat eb pj C b -∗
  (* the general path's whole credential (persistent) *)
  printk_env γpr γd γv -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ mf : regfile,
    sie_cap_gpr mf K b pj -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    cpu_own 0%nat eb pj C b -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

(* printk's contract as a PROP, so a caller can carry it as a HYPOTHESIS
   rather than instantiate a functor.  [wp_printk_gen_sconf_body] has Coq-arrow
   premises ([38 <= K], [nonul f], ...), so it is NOT an [iProp] and cannot be
   boxed the way [SpecPanic.panic_wp_any] is; this is the [Prop] twin of that
   idiom, and the same one [ProofBmap.balloc_contract] already uses.

   WHY IT MATTERS: [PRINTK_GEN]'s only instance is [LinkPrintkGen]'s own
   [Axiom], so a function that instantiated the functor would carry that axiom
   into its own [Print Assumptions] -- and, through any caller, into theirs.
   Carrying the contract as a hypothesis instead keeps such a function at the
   standing six and pushes the obligation up to whoever finally discharges it,
   exactly as [panic_wp_any] is pushed.  balloc's out-of-blocks arm is the
   first fs.c consumer. *)
Definition printk_gen_contract `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId}
    (γpr : gname) (γd : uart_names) (γv : disk_names) : Prop :=
  forall (CIDp : CpuId) 
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) (b : bool),
    wp_printk_gen_sconf_body (CID := CIDp) γpr γd γv m0 K eb pj C dqf f descs b.

Module Type PRINTK_GEN.
  Parameter wp_printk_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{GEN : GenId} `{CID : CpuId}
      (γpr : gname) (γd : uart_names) (γv : disk_names) (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc) (b : bool),
      wp_printk_gen_sconf_body γpr γd γv m0 K eb pj C dqf f descs b.
End PRINTK_GEN.

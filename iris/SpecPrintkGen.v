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
   contract (claude-notes/projects/printk.md), so it is assumed here and main's
   proof is a functor over it; proving it later replaces exactly the [Axiom].

   Everything about the format string and the varargs is UNCHANGED and reused
   from SpecPrintk.v ([pk_arg_desc], [pk_desc_res], [pk_vararg], [pk_kinds]) --
   the caller's obligations do not depend on which path runs.  Three things
   differ:

   1. THE FLAGS ARE NOT THREADED.  The general contract must NOT require
      [panicking = 0]: requiring it would force a fraction of the cell into
      every caller's precondition AND forbid panic() from ever writing it.
      printk works whichever way the flag reads -- it only decides whether the
      lock is taken -- so both flag cells live in their own invariant
      ([printk_flags_inv]) inside [printk_env], and no caller mentions them.

   2. THE TRANSMITTER RIDES UNDER pr.lock.  On the panic path the caller owns
      [uart_tx_own]/[uart_sent] outright and printk threads them.  On the
      general path pr.lock is what serializes output, so the exclusive
      transmitter token is exactly what it protects ([pr_res]) -- that is the
      only transmit-rights story available, since uartputc_sync's proven
      contract takes token + receipt and nothing else can mint them.  The
      consequence for the post is that printk promises nothing about the trace:
      the receipt it earned went back under the lock.

   3. THE GENERAL PATH TAKES A LOCK, so acquire's cone comes with it:
      [cpu_own] threaded net-zero (printk leaves the interrupt level as it
      found it) plus the tp/cid convention, and [panic_wp] for acquire's
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
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import PrintkFmt.
Require Import SpecPanic.
Require Import SpecPrintk.
From Kernel Require KernelSyms.

(* the [pr] lock, the one object the general path touches that the panic path
   does not.  [static struct { struct spinlock lock; } pr;] -- the lock is the
   FIRST field, so the object's address IS the lock's. *)
Definition pr_lock : mword 64 := mword_of_int KernelSyms.pr.

Section SpecPrintkGen.
  Context `{!riscvGS Σ, !sieG Σ, !lockG Σ}.
  Context `{!uartGhostG Σ, !diskGhostG Σ}.
  Context `{CID : CpuId}.

  (* ------------------------------------------------------------------- *)
  (* The two panic flags, in their OWN invariant.                         *)
  (* Nothing about the pair is asserted -- the invariant exists so that    *)
  (* printk can read [panicking] (and, on the panicked path, spin on       *)
  (* [panicked]) without any caller owning either cell, and so that        *)
  (* panic() remains free to write both.                                  *)
  (* ------------------------------------------------------------------- *)
  Definition printkFlagsN : namespace := nroot .@ "printkflags".

  Definition printk_flags_inv : iProp Σ :=
    inv printkFlagsN
      (∃ pv pkv : mword 32,
         (mword_of_int KernelSyms.panicking : mword 64) ↦₄ pv ∗
         (mword_of_int KernelSyms.panicked : mword 64) ↦₄ pkv).

  Global Instance printk_flags_inv_persistent : Persistent printk_flags_inv.
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------- *)
  (* What pr.lock protects: THE TRANSMITTER.                              *)
  (* pr.lock does not guard any C data -- it exists to keep two harts'     *)
  (* output from interleaving mid-line.  In separation logic that is       *)
  (* exactly "it owns the right to push bytes": the exclusive token plus   *)
  (* the mono-list receipt for what has been pushed so far, which is the   *)
  (* pair uartputc_sync's contract consumes and returns.                  *)
  (* ------------------------------------------------------------------- *)
  Definition pr_res (γd : uart_names) : iProp Σ :=
    (∃ l : list (bv 8), uart_tx_own γd l ∗ uart_sent γd l)%I.

  (* ------------------------------------------------------------------- *)
  (* The whole general-path credential, and it is PERSISTENT -- which is   *)
  (* what lets it cross main's [started] invariant to the other harts for  *)
  (* free (claude-notes/projects/main-boot.md).                            *)
  (* ------------------------------------------------------------------- *)
  Definition printk_env (γpr : gname) (γd : uart_names) (γv : disk_names) : iProp Σ :=
    (is_lock γpr pr_lock "pr"%string (pr_res γd) ∗
     uart_dlab_off γd ∗
     dev_inv γd γv ∗
     printk_flags_inv)%I.

  Global Instance printk_env_persistent γpr γd γv : Persistent (printk_env γpr γd γv).
  Proof. apply _. Qed.

End SpecPrintkGen.

Definition wp_printk_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ}
    `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
    (γ γpr : gname) (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
    (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
    (dqf : dfrac) (f : string) (descs : list pk_arg_desc) :=
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
  (* the tp/cid convention acquire's push_off cone requires *)
  m0 !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  sie_cap_gpr γ m0 K -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp -∗
  (* the interrupt level is left exactly as found: acquire/release pair *)
  cpu_own γ 0%nat eb pj C -∗
  (* the general path's whole credential (persistent) *)
  printk_env γpr γd γv -∗
  fmt ↦ₛ{ dqf } f -∗
  ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
  ( ∀ mf : regfile,
    sie_cap_gpr γ mf K -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    cpu_own γ 0%nat eb pj C -∗
    fmt ↦ₛ{ dqf } f -∗
    ([∗ list] j ↦ d ∈ descs, pk_desc_res (pk_vararg m0 j) d) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PRINTK_GEN.
  Parameter wp_printk_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ}
      `{!uartGhostG Σ, !diskGhostG Σ} `{CID : CpuId}
      (γ γpr : gname) (γd : uart_names) (γv : disk_names) (Φ : mval -> iProp Σ)
      (m0 : regfile) (K : nat) (eb : bool) (pj : mword 64) (C : iProp Σ)
      {dqf : dfrac} (f : string) (descs : list pk_arg_desc),
      wp_printk_gen_sconf_body γ γpr γd γv Φ m0 K eb pj C dqf f descs.
End PRINTK_GEN.

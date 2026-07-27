(* SpecPanic.v -- the panic() contract.

   panic() prints and then spins forever, so it NEVER returns: a safety-only
   WP for it holds with ANY postcondition, and a caller that reaches it has
   discharged its own goal.  [panic_wp] is that statement, as a persistent
   resource threaded by every spec whose function sits above a panic call
   (acquire's "already holding" arm, kvmmap's failure arm, ...).

   It is the one deliberately ASSUMED contract of the lock layer (an eventual
   lemma: uartputc + a Löb spin loop -- as myproc once was, now proven).
   Keeping it here rather than inside one subsystem's spec file lets the
   spinlock layer and the kvm chain share the single statement. *)
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes KernelText.
Require Import SmodeCore.
Require Import IntrDefs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section Panic.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  (* a0 = msg.  Everything else the caller still holds is simply dropped. *)
  Definition panic_wp : iProp Σ :=
    (□ ∀ (Φ : mval -> iProp Σ) (γ : gname) (m : regfile) (avail : nat),
       kernel_text -∗ pc_is (mword_of_int KernelSyms.panic) -∗ sie_cap_gpr γ m avail -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Global Instance panic_wp_persistent : Persistent panic_wp.
  Proof. apply _. Qed.

End Panic.

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
Require Import RegFile HartTp WpNext.
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
    (□ ∀ (Φ : mval -> iProp Σ) (m : regfile) (avail : nat) (b : bool),
       kernel_text -∗ pc_is (mword_of_int KernelSyms.panic) -∗ sie_cap_gpr m avail b -∗
       WP (Loop : expr riscv_lang) {{ Φ }})%I.

  Global Instance panic_wp_persistent : Persistent panic_wp.
  Proof. apply _. Qed.

End Panic.

(* ---------------------------------------------------------------------- *)
(* THE HART-GENERIC FORM.  panic() prints and spins forever on WHATEVER    *)
(* hart reaches it, so its contract is available at every hart at once.    *)
(* A function that can PARK does not return on the hart it entered on      *)
(* (SwtchCtx.v's migratable records), so a post-resume half that still     *)
(* has a panic arm to discharge -- sleep's re-acquire of the condition     *)
(* lock is the one that does -- needs the contract at the RESUMING hart.   *)
(* Every parking contract above sched threads this form instead of the     *)
(* ambient one; non-parking callers use the bridge below.                  *)
(*                                                                          *)
(* EXPLICIT-CPUID NOTE (kept, not collapsed here): [panic_wp] already      *)
(* quantifies [CID] via its section [Context], so inside a [wp_next]       *)
(* continuation it resolves at the REBOUND hart with no annotation and no  *)
(* need to go through this wrapper -- a post-resume half reached that way  *)
(* can apply [panic_wp] directly.  [panic_wp_any] / [panic_wp_any_at] were *)
(* the bridge needed only because [CID] used to be ambient (fixed at the   *)
(* ENTRY hart for the whole file); that reason is gone.  They are left in  *)
(* place because 13 consumer files (ProofAcquiresleep.v, ProofBread.v,     *)
(* ProofBwrite.v, ProofSleep.v, SpecAcquiresleep.v, SpecBread.v,           *)
(* SpecBwrite.v, SpecPiperead.v, SpecPipewrite.v, SpecSleep.v,             *)
(* SpecSysPause.v, SpecUartwrite.v, SpecVirtioDiskRw.v) still thread this  *)
(* form and are out of this port's scope; retiring it is a consumer-side   *)
(* cleanup for whoever ports those files, not a change owed here.          *)
(* ---------------------------------------------------------------------- *)
Definition panic_wp_any `{!riscvGS Σ, !sieG Σ} : iProp Σ :=
  (□ ∀ h : CPU, panic_wp (CID := h))%I.

Global Instance panic_wp_any_persistent `{!riscvGS Σ, !sieG Σ} :
  Persistent panic_wp_any.
Proof. rewrite /panic_wp_any. apply _. Qed.

Lemma panic_wp_any_at `{!riscvGS Σ, !sieG Σ} (h : CPU) :
  panic_wp_any -∗ panic_wp (CID := h).
Proof.
  iIntros "#H". rewrite /panic_wp_any.
  iPoseProof (bi.forall_elim h with "H") as "H2". iExact "H2".
Qed.

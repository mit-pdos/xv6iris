(* PanicStub.v -- THE PLACEHOLDER panic() CREDENTIAL, ON ITS WAY OUT.
   panic()'s real contract is [SpecPanic.wp_panic_sconf_body], proved from
   printk.c's fourteen instructions in ProofPanic.v; this file is what the
   tree threaded before there was one, and it survives only until that proof
   is spliced into the call sites.

   [panic_wp] says: at pc = panic, with the machine capability and nothing
   else, [WP Loop] holds -- panic prints and spins forever, so a safety-only
   WP for it holds with ANY postcondition and a caller that reaches it has
   discharged its own goal.  The no-postcondition half is right and survives
   into the real contract.  The precondition does NOT: it asks for no message
   string (so [printk("%s\n", s)] would read memory nobody owns), no stack
   budget (so the frame push would run off the stack), and no interrupt/lock
   accounting.  It is therefore not derivable from the code, which is why
   LinkPanicStub.v supplies it with an [Axiom].

   WHY IT CANNOT SIMPLY BE DELETED YET.  printk's own precondition asks for
   [panic_wp_any] (acquire's "already holding" arm), so ProofPanic.v has to
   hand printk one -- the C-level panic -> printk -> acquire -> panic cycle
   showing through.  Replacing this credential with the real contract means
   giving acquire, and hence every caller of acquire, printk's environment;
   that is the splice, and it closes by Löb at panic (the frame push is a
   step, so the later strips).  Until then the two coexist and this one is
   named for what it is.

   169 files thread it, so the names [panic_wp] / [panic_wp_any] /
   [panic_wp_any_at] are left exactly as they were: renaming them would churn
   every one of those files twice. *)
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
  Context `{GEN : GenId} `{CID : CpuId}.

  (* a0 = msg.  Everything else the caller still holds is simply dropped. *)
  Definition panic_wp : iProp Σ :=
    (□ ∀ (m : regfile) (avail : nat) (b : bool) (p : mword 64),
       kernel_text -∗ pc_is (mword_of_int KernelSyms.panic) -∗
       sie_cap_gpr m avail b p -∗
       WP (Loop : expr riscv_lang))%I.

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
(* The real contract does not need the pair: [SpecPanic]'s is hart-generic *)
(* by construction (the [∀ h : CPU] is inside its own box), which is what  *)
(* the split below should have been all along.                             *)
(* ---------------------------------------------------------------------- *)
Definition panic_wp_any `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} : iProp Σ :=
  (□ ∀ h : CPU, panic_wp (CID := h))%I.

Global Instance panic_wp_any_persistent `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} :
  Persistent panic_wp_any.
Proof. rewrite /panic_wp_any. apply _. Qed.

Lemma panic_wp_any_at `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} (h : CPU) :
  panic_wp_any -∗ panic_wp (CID := h).
Proof.
  iIntros "#H". rewrite /panic_wp_any.
  iPoseProof (bi.forall_elim h with "H") as "H2". iExact "H2".
Qed.

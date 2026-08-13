(* LinkPanicStub.v -- the one place the PLACEHOLDER panic() credential
   ([PanicStub.panic_wp], see that file's header) is ASSUMED.

   panic() ITSELF IS PROVEN: [LinkPanic.v] seals [PanicProof Printk : PANIC]
   against [SpecPanic.wp_panic_sconf_body].  What is still assumed here is the
   WEAKER, resource-free credential the 169 files above a panic call currently
   thread -- acquire's "already holding" arm, kvmmap's failure arm, the printk
   cone, main (both arms) -- which is not derivable from the code (it names no
   message string and no stack budget) and which the real contract replaces
   when those call sites are spliced.  [tools/proof_coverage.py] reports it
   with the Axiom named here.

   Written out with an explicit [Axiom] rather than a [Declare Module]: both are
   visible to [Print Assumptions], but only the keyword is visible to the
   coverage tool's textual axiom scan. *)
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import PanicStub.

Module PanicAssumed.
  (* THE AMBIENT-HART FORM is the primitive: panic() prints and spins on
     WHATEVER hart reaches it, so the contract is available at every hart, and
     the hart-generic [panic_wp_any] is a consequence rather than a second
     assumption (see [panic_wp_any_holds] below). *)
  Axiom panic_wp_holds :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId},
      ⊢ panic_wp.
End PanicAssumed.

(* the form every client above sched threads ([SpecMain] / [SpecMainSecondary]
   both ask for this one), out of the ambient contract at each hart.

   NB the [∀] is introduced with [bi.forall_intro] at the META level, not with
   [iIntros]: the body is a BARE CID-indexed atom, and the proofmode refuses to
   see [(∀ h : CPU, panic_wp)%I] as a universal quantifier at all ("iIntro:
   cannot turn ... into a universal quantifier" -- the intro half of
   durable-notes' [iSpecialize] trap, whose [bi.forall_elim] escape is
   [PanicStub.panic_wp_any_at]). *)
Lemma panic_wp_all `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} :
  ⊢ ∀ h : CPU, panic_wp (CID := h).
Proof. apply bi.forall_intro. intros h. apply PanicAssumed.panic_wp_holds. Qed.

Lemma panic_wp_any_holds `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} :
  ⊢ panic_wp_any.
Proof.
  rewrite /panic_wp_any. iModIntro.
  iPoseProof panic_wp_all as "H". iExact "H".
Qed.

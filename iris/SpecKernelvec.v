(* SpecKernelvec.v -- the public interface of kernelvec, stated independently
   of its proof.  Requires only the definitional layer (IntrDefs and below) --
   never a whole-function proof file -- so the interrupt tier can be built
   against it without pulling kernelvec's proof cone.

   kernelvec is xv6's S-mode trap vector (kernelvec.S): it opens a 256-byte
   frame under sp, saves the 17 caller-saved registers, calls kerneltrap(),
   restores them, closes the frame and SRETs back to the interrupted pc.

   Its public contract is therefore NOT a callable-function spec -- nothing
   jumps to kernelvec, the hardware traps to it -- but the interrupt-handler
   contract [IntrDefs.intr_handler_spec]: a trap into kernelvec returns
   idempotently to the interrupted pc with SIE re-enabled, the register file
   preserved and the per-trap frame intact.  That is [KERNELVEC] below, and it
   is the only thing the seal lets out; the entry-to-SRET WP it is built from
   ([wp_kernelvec], with its explicit mstatus/menvcfg parameters and their
   well-formedness premises) is an internal step of [ProofKernelvec.v].

   Also here, because callers' STATEMENTS need them and their proofs are pure
   [vm_compute]s: the two trap-vector facts that [IntrDefs.intr_inv_alloc]
   asks for when the handler is kernelvec.                                   *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvFetchExec.
Require Import MinstretInv.
Require Import SmodeCore KernelText.
Require Import WpIntrCore.
Require Import IntrDefs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Notation KV := KernelSyms.kernelvec.

(* the kernelvec trap-vector facts (Direct mode, base = itself) -- feed
   [intr_inv_alloc] when the handler is kernelvec. *)
Lemma kernelvec_tv_direct :
  trapVectorMode_forwards
    (_get_Mtvec_Mode (mword_of_int KernelSyms.kernelvec : mword 64)) = TV_Direct.
Proof. vm_compute. reflexivity. Qed.

Lemma kernelvec_stvec_base :
  stvec_base (mword_of_int KernelSyms.kernelvec : mword 64)
    = (mword_of_int KernelSyms.kernelvec : mword 64).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Definition kernelvec_handler_spec_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} :=
  hw_config -∗
  minstret_inv -∗
  kernel_text -∗
  intr_handler_spec (mword_of_int KernelSyms.kernelvec : mword 64).

Module Type KERNELVEC.
  Parameter kernelvec_handler_spec :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId},
      kernelvec_handler_spec_body.
End KERNELVEC.

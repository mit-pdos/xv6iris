(* SpecSpin.v -- the public interface of [spin], stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   The [spin] symbol at 0x8000001a (just past _entry's [jal start]) is a single
   compressed self-jump [c.j spin] = [0xa001], the halt loop each hart runs
   forever once start() returns.  So the spec has NO continuation: [spin] never
   leaves the self-jump, and the theorem is simply that the machine keeps
   running (WP Loop) given the M-mode config, an all-permissive PMP and the
   register file. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base.
Require Import RiscvLang RegFile RiscvPtsto RiscvFetchExec WpGpr.
Require Import InstrBytes KernelText.
From Kernel Require KernelSyms.
Require Import TsoCtx.
Local Open Scope Z_scope.

(* the entry pc of the park loop (also its jump target -- the loop is a
   self-jump, so the two coincide). *)
Definition pc_spin : mword 64 := mword_of_int KernelSyms.spin.

Definition wp_spin_body `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (m : regfile)
    (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp) :=
  pmp_allows_all pmpcfg0 ->
  mmode_config (DfracOwn q) -∗
  pmpcfg_n ↦ᵣ{DfracOwn q} pmpcfg0 -∗
  pc_is pc_spin -∗
  gpr_file m -∗
  kernel_text -∗
  WP (Loop : expr riscv_lang).

Module Type SPIN.
  Parameter wp_spin :
    forall `{!riscvGS Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx} (m : regfile)
      (pmpcfg0 : type_of_register pmpcfg_n) (q : Qp),
      wp_spin_body m pmpcfg0 q.
End SPIN.

(* WpUserLoop.v -- the Löb capstone of the user-execution theorem.

   [wp_user_loop]: IF one machine step from any state satisfying the
   user frame [P] either re-establishes [P] (the instruction retired:
   compute, branch, successful load/store) or hands the trap resources
   [Tr] to the kernel re-entry continuation (ecall, page fault, illegal
   instruction, interrupt), THEN the machine may run user code forever:
   WP Loop holds from [P] with only the kernel re-entry continuation.

   The step obligation [USTEP] receives both continuations UNDER A
   LATER -- exactly what the step engines provide (wp_exec_step_trapish_inv
   and the retire-path engines hand their continuation back under ▷,
   having consumed one physical machine step) -- and the Löb induction
   hypothesis plugs into the retire slot.

   This pins the interface: the grand per-instruction case analysis
   (fetch trichotomy x decode totality x execute families) discharges
   [USTEP] with P := the user frame (config cells + upt_inv + arbitrary
   gpr_file + arbitrary pc) and Tr := the trapped-machine resources
   (Supervisor, trap CSRs written, pc_is stvec_base).                  *)
From Stdlib Require Import ZArith.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Local Open Scope Z_scope.

Section WpUserLoop.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.

  (* the two continuations are an ADDITIVE conjunction: the step's prover
     case-analyzes the machine state first and then selects exactly one *)
  Lemma wp_user_loop (P Tr : iProp Σ) E (Φ : mval -> iProp Σ) :
    □ (P -∗
       ▷ ((P -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) ∧
          (Tr -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }})) -∗
       WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    P -∗
    (Tr -∗ WP (Loop : expr riscv_lang) @ E {{ Φ }}) -∗
    WP (Loop : expr riscv_lang) @ E {{ Φ }}.
  Proof.
    iIntros "#Hstep".
    iLöb as "IH".
    iIntros "HP Htrap".
    iApply ("Hstep" with "HP").
    iNext. iSplit.
    - iIntros "HP". iApply ("IH" with "HP Htrap").
    - iExact "Htrap".
  Qed.

End WpUserLoop.

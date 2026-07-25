(* CpuOwn.v -- ownership of THIS cpu's [struct cpu] plus the push/pop
   interrupt discipline, as ONE predicate.

   [cpu_own γ n eb p C] owns, for the ambient CpuId:
     - cpus[cid].noff  ↦₄ n            -- the CELL IS the count level, so
                                          push/pop specs need no noff
                                          argument and no level-mirror
                                          premise;
     - cpus[cid].intena               -- pinned to [eb] (the saved base
                                          enable state) while n ≥ 1;
                                          arbitrary at level 0;
     - the counting token [intr_count γ n eb] (IntrDefs.v) -- the SIE
       ghost eighth + (at n ≥ 1, eb = true) the restore payload;
     - cpus[cid].proc  ↦₈ p            -- the current-process field
                                          (the former [cur_proc p],
                                          inlined here);
     - [C], the context-slot payload for cpus[cid].context:
       [cpu_ctx_free] at boot and while the scheduler itself runs; the
       scheduler tier instantiates it with the parked scheduler
       continuation (▷ sched_vc (a_cpu_ctx cid), SchedCtx.v).  Functions
       indifferent to the slot are ∀C-parametric and carry it opaquely.

   [cpu_own γ 0 false p cpu_ctx_free] is constructible from raw boot
   resources (cells + the SIE eighth at '0') -- no trap handler, no
   stvec, no trap CSRs -- which is what makes push_off/pop_off (and the
   whole acquire/release cone above them) usable during early boot,
   where both are no-ops on SIE. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import SmodeCore.
Require Import IntrDefs.
Require Import ProcGeom.
Local Open Scope Z_scope.

Definition noff_val (n : nat) : mword 32 := mword_of_int (Z.of_nat n).
Definition intena_val (eb : bool) : mword 32 :=
  if eb then mword_of_int 1 else mword_of_int 0.

Section CpuOwn.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{CID : CpuId}.

  Definition cpu_own (γ : gname) (n : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) : iProp Σ :=
    (⌜ (Z.of_nat n < 2 ^ 31)%Z ⌝ ∗
     a_cpu_noff cid_word ↦₄ noff_val n ∗
     (match n with
      | O => (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv)%I
      | S _ => a_cpu_int cid_word ↦₄ intena_val eb
      end) ∗
     intr_count γ n eb ∗
     a_cpu_proc cid_word ↦₈ p ∗
     C)%I.

  (* boot entry: raw cells + the SIE eighth at '0'.  [iv] arbitrary. *)
  Lemma cpu_own_init_boot (γ : gname) (p : mword 64) (nv iv : mword 32)
      (C : iProp Σ) :
    nv = noff_val 0 ->
    a_cpu_noff cid_word ↦₄ nv -∗
    a_cpu_int cid_word ↦₄ iv -∗
    intr_off_tok γ -∗
    a_cpu_proc cid_word ↦₈ p -∗
    C -∗
    cpu_own γ 0 false p C.
  Proof.
    intros ->. iIntros "Hnoff Hint Htok Hproc HC".
    iFrame "Hnoff Hproc HC".
    iSplitR. { iPureIntro. vm_compute. reflexivity. }
    iSplitL "Hint". { iExists iv. iExact "Hint". }
    iApply (intr_count_init_off with "Htok").
  Qed.

  (* swap the context-slot payload (e.g. park / unpark the scheduler
     continuation) without disturbing the rest. *)
  Lemma cpu_own_ctx_swap (γ : gname) (n : nat) (eb : bool) (p : mword 64)
      (C C' : iProp Σ) :
    cpu_own γ n eb p C -∗ (C -∗ C') -∗ cpu_own γ n eb p C'.
  Proof.
    iIntros "(%Hbound & Hnoff & Hint & Hcnt & Hproc & HC) HW".
    iSplitR; [done |]. iFrame "Hnoff Hint Hcnt Hproc". iApply ("HW" with "HC").
  Qed.

  (* retarget the proc field (the scheduler's c->proc writes). *)
  Lemma cpu_own_set_proc (γ : gname) (n : nat) (eb : bool)
      (p p' : mword 64) (C : iProp Σ) :
    cpu_own γ n eb p C -∗
    (a_cpu_proc cid_word ↦₈ p ∗
     (a_cpu_proc cid_word ↦₈ p' -∗ cpu_own γ n eb p' C)).
  Proof.
    iIntros "(%Hbound & Hnoff & Hint & Hcnt & Hproc & HC)".
    iFrame "Hproc". iIntros "Hproc". iSplitR; [done |]. iFrame.
  Qed.
End CpuOwn.

(** * WkGprAcc.v — the TWO-CELL [gpr_file] accessor (M4 batch 4)

    [WpGpr.gpr_file_lookup_acc]/[gpr_file_insert_acc] extract ONE register
    cell; a whole-function chain that feeds a CELL-based leaf taking two GPR
    cells at once (the c.sdsp/c.ldsp memory leaves: base [sp] plus the
    data/destination register) needs both out simultaneously, and the
    single-cell wand cannot be iterated (the remainder is not exposed as a
    file).  This is the two-key accessor, proved once over [rf_to_gmap]'s
    map algebra.  The wand takes both cells back at ARBITRARY values, so it
    serves read-read (c.sdsp: apply at the unchanged values) and read-write
    (c.ldsp: apply at the reloaded destination) sites alike.

    New file rather than a [WpGpr.v] edit: the batch-4 units are new-files-
    only (concurrent agents build against the existing [.vo] tree). *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base RiscvLang RegFile RiscvPtsto WpGpr.

Section wk_gpr_acc.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Lemma gpr_file_acc_2 (f : regfile) (i j : regidx) :
    i ≠ j ->
    gpr_file f ⊢ gpr_pt i (f i) ∗ gpr_pt j (f j) ∗
      (∀ wi wj : mword 64,
         gpr_pt i wi -∗ gpr_pt j wj -∗
         gpr_file (<[i := wi]> (<[j := wj]> f))).
  Proof.
    intro Hij.
    assert (Hji : j ≠ i) by (intro He; apply Hij; by symmetry).
    unfold gpr_file. iIntros "[_ Hm]".
    iDestruct (big_sepM_delete _ _ i _ (rf_to_gmap_lookup f i) with "Hm")
      as "[$ Hm]".
    assert (Hjd : delete i (rf_to_gmap f) !! j = Some (f j)).
    { rewrite lookup_delete_ne; [apply rf_to_gmap_lookup | exact Hij]. }
    iDestruct (big_sepM_delete _ _ j _ Hjd with "Hm") as "[$ Hm]".
    iIntros (wi wj) "Hpi Hpj".
    iSplitR; [iApply gpr_file_dom |].
    rewrite !rf_to_gmap_upd.
    (* <[i:=wi]> (<[j:=wj]> M) over the double-deleted remainder *)
    assert (Heq : (<[i := wi]> (<[j := wj]> (rf_to_gmap f)) : gmap regidx _)
                  = <[i := wi]> (<[j := wj]> (delete j (delete i (rf_to_gmap f))))).
    { symmetry. rewrite insert_delete_insert.
      rewrite <- (delete_insert_ne _ i j wj Hij).
      apply insert_delete_insert. }
    rewrite Heq.
    iApply big_sepM_insert.
    { rewrite lookup_insert_ne; [| exact Hji].
      rewrite lookup_delete_ne; [apply lookup_delete | exact Hji]. }
    iFrame "Hpi".
    iApply big_sepM_insert.
    { apply lookup_delete. }
    iFrame "Hpj". iExact "Hm".
  Qed.

End wk_gpr_acc.

Print Assumptions gpr_file_acc_2.

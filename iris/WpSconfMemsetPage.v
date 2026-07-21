(* WpSconfMemsetPage.v -- the PAGE-LEVEL memset WP over the SIE-agnostic sconf
   world.  [wp_memset_page_sconf] is now a THIN WRAPPER over the general
   whole-function memset spec [MEMSET.wp_memset_sconf] (WpMemsetArray.v)
   instantiated at the fixed page count len = 4096: it bridges [page_own p] to
   memset's per-byte buffer, derives the general spec's bound preconditions
   (nonzero count, 32-bit count, no 2^64 wraparound) from [page_valid p], and
   rebuilds [page_own p] from the written buffer on the way out. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes.
Require Import WpGpr.
Require Import RegFile.
Require Import WpMmodeLeafBase.
Require Import SmodeCore KernelText WpMemsetS.
Require Import WpMemsetPage.
Require Import CalleeSaved.
Require Import StackOwn.
Require Import KallocInv.
Require Import IntrDefs.
Require Import SpecMemset.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import KptTree.
Require Import Riscv.rv64d.
Require Import SpecMemsetPage.
Import Defs.


Module MemsetPageProof (MemsetArray : MEMSET) : MEMSETPAGE.

Section WpSconfMemsetPage.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{CID : CpuId}.

  Lemma wp_memset_page_sconf (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (cval : mword 64)
    : wp_memset_page_sconf_body γ root_ppn Φ m0 n cval.
  Proof.
    cbv beta delta [wp_memset_page_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt Hn Hpv Hcval Ha2 Hret0.
    iIntros "Hsc Hhs Hcg Htlbinv #Htext Hpc Hpage Hcont".
    (* --- bridge [page_own p] to memset's per-byte buffer --- *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hbuf".
    (* --- derive the general spec's bound preconditions from [page_valid] --- *)
    assert (Ha2' : m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite Ha2; f_equal; vm_compute; reflexivity).
    assert (Hnw : uint p + Z.of_nat 4096 < 2 ^ 64).
    { destruct Hpv as [_ [_ Hhi]]. unfold kmem_hi in Hhi.
      change (Z.of_nat 4096) with 4096. change (2 ^ 64) with 18446744073709551616. lia. }
    (* --- apply the general memset spec at len = 4096 --- *)
    iApply (MemsetArray.wp_memset_sconf γ root_ppn Φ m0 n 4096 cval olds
              Hn ltac:(lia) ltac:(vm_compute; reflexivity) Hnw Hcval Ha2' Hret0
              with "Hsc Hhs Hcg Htlbinv Htext Hpc [Hbuf] [-]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". iExact "H". }
    iIntros (mfin) "Hsc Hhs Hcg Htlbinv Hpc Hbuf %Hcs".
    (* rebuild page_own from the all-cbyte buffer *)
    iApply ("Hcont" $! mfin with "Hsc Hhs Hcg Htlbinv Hpc [Hbuf] [%]").
    - iEval (rewrite /page_own /byte_any).
      iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". iExists _. iExact "H".
    - exact Hcs.
  Qed.

End WpSconfMemsetPage.

End MemsetPageProof.

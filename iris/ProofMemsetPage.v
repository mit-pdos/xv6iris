(* ProofMemsetPage.v -- the PAGE-LEVEL memset WP over the SIE-agnostic sconf
   world.  [wp_memset_page_sconf] is now a THIN WRAPPER over the general
   whole-function memset spec [MEMSET.wp_memset_sconf] (WpMemsetArray.v)
   instantiated at the fixed page count len = 4096: it bridges [page_own p] to
   memset's per-byte buffer and rebuilds [page_own p] from the written buffer
   on the way out. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.riscv_extras.
Require Import RiscvModelBytes.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpNext.
Require Import WpMemsetPage.
Require Import KallocInv.
Require Import SpecMemset.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Require Import Riscv.rv64d.
Require Import SpecMemsetPage.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.


Module MemsetPageProof (MemsetArray : MEMSET) : MEMSETPAGE.

Section ProofMemsetPage.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Context {kt : ktier}.
  Lemma wp_memset_page_val_sconf
      (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64)
    : wp_memset_page_val_sconf_body kt m0 n cval b pcur.
  Proof.
    cbv beta delta [wp_memset_page_val_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt cbyte Hn Hpv Hcval Ha2.
    iIntros "Hcg #Htext Hpc Hpage Hcont".
    (* --- bridge [page_own p] to memset's per-byte buffer --- *)
    iEval (rewrite /page_own /byte_any) in "Hpage".
    iDestruct (bytes_choose 4096 0 (fun j b => ((pa_add p j) ↦ₘ b)%I) with "Hpage")
      as (olds) "Hbuf".
    (* --- the count register holds 4096 --- *)
    assert (Ha2' : m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat 4096) : mword 64))
      by (rewrite Ha2; f_equal; vm_compute; reflexivity).
    (* --- apply the general memset spec at len = 4096 --- *)
    iApply (MemsetArray.wp_memset_sconf kt KT0 m0 n 4096 cval olds b pcur
              Hn ltac:(vm_compute; reflexivity) Hcval Ha2'
              with "Hcg Htext Hpc [Hbuf]").
    { iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". iExact "H". }
    iIntros (CID1 Hs1 mfin) "Hcg Hpc Hbuf %Hcs".
    iSpecialize ("Hcont" $! CID1 with "[]"); [iPureIntro; exact Hs1|].
    (* the bytes come back NAMED -- that is the whole of this form *)
    iApply ("Hcont" $! mfin with "Hcg Hpc [Hbuf] [%]").
    - iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H". iExact "H".
    - exact Hcs.
  Qed.

  (* ...and the contents-existential form, by forgetting them *)
  Lemma wp_memset_page_sconf
      (m0 : regfile) (n : nat) (cval : mword 64) (b : bool) (pcur : mword 64)
    : wp_memset_page_sconf_body kt m0 n cval b pcur.
  Proof.
    cbv beta delta [wp_memset_page_sconf_body].
    intros a0_idx a1_idx a2_idx pcE ra0 p ret_tgt Hn Hpv Hcval Ha2.
    iIntros "Hcg #Htext Hpc Hpage Hcont".
    iApply (wp_memset_page_val_sconf m0 n cval b pcur Hn Hpv Hcval Ha2
              with "Hcg Htext Hpc Hpage").
    rewrite /wp_next. iIntros (CID1) "%Hs1".
    iSpecialize ("Hcont" $! CID1 with "[]"); [iPureIntro; exact Hs1|].
    iIntros (mfin) "Hcg Hpc Hbuf %Hcs".
    iApply ("Hcont" $! mfin with "Hcg Hpc [Hbuf] [%]"); [| exact Hcs].
    iEval (rewrite /page_own /byte_any).
    iApply (big_sepL_impl with "Hbuf"). iIntros "!>" (k j _) "H".
    iExists _. iExact "H".
  Qed.

End ProofMemsetPage.

End MemsetPageProof.

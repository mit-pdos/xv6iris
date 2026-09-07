(* CtxBirth.v -- relaxed-ww RULING C (relaxed-ww.md §2.4, the owner's): a
   lock's birth takes the creator's FLUSHED token (§2.14), and the creators
   whose proofs hold no fence -- boot's [initlock] callers ([kinit],
   [procinit], [initlog], the icache/bcache boot folds) and [pipealloc] --
   have only the running one.  Until the ruling lands ((c1) born tokens with
   a born-acquire class over the generic callers, or (c2) the twin's
   author-indexed record for births only), those sites borrow a flushed
   token off the running one through the ONE bridge below and hand it back.
   It is NOT derivable: nothing here says the creator's stores drained.  Its
   consumers are exactly the birth sites listed in relaxed-ww.md §2.15b;
   nothing else may import this file.  relaxed-ww STAGE E *)
From Stdlib Require Import ZArith Lia.
From stdpp Require Import bitvector.definitions gmap.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import dfrac auth.
From iris.base_logic.lib Require Import ghost_var ghost_map mono_nat gen_heap.
Require Import SailStdpp.Values.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes RiscvLang RiscvPtsto Ktier.
Require Import TsoMemPa TsoGhost.
Require Import TsoCtx.

Section birth.
  Context `{!riscvGS Σ}.

  Lemma own_context_flushed_birth_RULING_C `{CID : CpuId} (ξ : CtxId) :
    own_context ξ ⊢
    ∃ Df : nat, own_context_flushed ξ Df ∗ (own_context_flushed ξ Df -∗ own_context ξ).
  Admitted.

End birth.

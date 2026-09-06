(* CpuOwnMorph.v -- the per-cpu bundle's transport along domination
   (A6.128, §0.43′).  [cpu_own] crosses swtch from the caller's thread to
   the target's on one hart; its cells ([cpus[h].noff/intena/proc]) are the
   caller's stores, still buffered, and the target reads them before any
   fence ([forkret]'s [myproc()], [release]'s [pop_off]).  The bundle owes
   [TsoCtx.CtxMorph], the one transport class; [ProofSwtch] moves it across
   swtch by the derived [TsoCtx.ctx_move].  This file is its instances, off
   [CpuOwn]'s public definitions (no [CpuOwn]/[IntrDefs] rebuild). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import Xv6G.
Require Import TsoCtx CtxMorphTac.
Local Open Scope Z_scope.

Section CpuOwnMorph.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Global Instance cur_proc_morph (p : mword 64) : CtxMorph (λ ξ, cur_proc (XI := ξ) p).
  Proof. rewrite /cur_proc. ctx_morph_solve. Qed.

  Global Instance cpu_cells_morph (n : nat) (eb : bool) (p : mword 64) :
    CtxMorph (λ ξ, cpu_cells (XI := ξ) n eb p).
  Proof. rewrite /cpu_cells. destruct n; ctx_morph_solve; apply cur_proc_morph. Qed.

  Global Instance cpu_priv_morph (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    CtxMorph (λ ξ, cpu_priv (XI := ξ) n eb p lks).
  Proof.
    rewrite /cpu_priv.
    apply ctx_morph_sep; [apply cpu_cells_morph |].
    apply ctx_morph_sep; apply ctx_morph_const.
  Qed.

  Global Instance cpu_hart_morph (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    CtxMorph (λ ξ, cpu_hart (XI := ξ) n eb p lks).
  Proof. rewrite /cpu_hart. apply ctx_morph_sep; [apply cpu_priv_morph | apply ctx_morph_const]. Qed.

  Global Instance cpu_own_morph (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    CtxMorph (λ ξ, cpu_own (XI := ξ) n eb p b lks).
  Proof. rewrite /cpu_own. apply ctx_morph_if; [apply ctx_morph_const | apply cpu_hart_morph]. Qed.

End CpuOwnMorph.

(* CpuOwnMove.v -- the per-cpu bundle's SAME-HART hand-off (A6.128, §0.43′).
   [cpu_own] crosses swtch from the caller's thread to the target's on one
   hart; its cells ([cpus[h].noff/intena/proc]) are the caller's stores, still
   buffered, and the target reads them before any fence ([forkret]'s
   [myproc()], [release]'s [pop_off]).  [TsoCtxMove.ctx_move] is the rule;
   this file is its instances for the bundle, off [CpuOwn]'s public
   definitions (no [CpuOwn]/[IntrDefs] rebuild). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var invariants.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang HartTp.
Require Import RegFile.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import LockSet.
Require Import CpuOwn.
Require Import Xv6G.
Require Import TsoCtx TsoCtxMove.
Local Open Scope Z_scope.

Section CpuOwnMove.
  Context `{!riscvGS Σ, !xv6G Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Global Instance cur_proc_move (p : mword 64) : CtxMove (λ ξ, cur_proc (XI := ξ) p).
  Proof. rewrite /cur_proc. ctx_move_solve. Qed.

  Global Instance cpu_cells_move (n : nat) (eb : bool) (p : mword 64) :
    CtxMove (λ ξ, cpu_cells (XI := ξ) n eb p).
  Proof. rewrite /cpu_cells. destruct n; ctx_move_solve; apply cur_proc_move. Qed.

  Global Instance cpu_priv_move (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    CtxMove (λ ξ, cpu_priv (XI := ξ) n eb p lks).
  Proof.
    rewrite /cpu_priv.
    apply ctx_move_sep; [apply cpu_cells_move |].
    apply ctx_move_sep; apply ctx_move_const.
  Qed.

  Global Instance cpu_hart_move (n : nat) (eb : bool) (p : mword 64) (lks : gset string) :
    CtxMove (λ ξ, cpu_hart (XI := ξ) n eb p lks).
  Proof. rewrite /cpu_hart. apply ctx_move_sep; [apply cpu_priv_move | apply ctx_move_const]. Qed.

  Global Instance cpu_own_move (n : nat) (eb : bool) (p : mword 64)
      (b : bool) (lks : gset string) :
    CtxMove (λ ξ, cpu_own (XI := ξ) n eb p b lks).
  Proof. rewrite /cpu_own. apply ctx_move_if; [apply ctx_move_const | apply cpu_hart_move]. Qed.

End CpuOwnMove.

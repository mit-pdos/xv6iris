(* WpGprCsrw.v -- split into Common/A/B for build parallelism; this shim re-exports everything. *)
From iris.base_logic.lib Require Import invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import SailStdpp.Base SailStdpp.TypeCasts.
Require Import RiscvLang RiscvPtsto WpGpr.
Local Open Scope Z_scope.

Require Export WpGprCsrwCommon WpGprCsrwA WpGprCsrwB.

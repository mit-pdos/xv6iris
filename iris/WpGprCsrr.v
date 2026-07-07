(* WpGprCsrr.v -- split into Common/A/B for build parallelism; this shim re-exports everything. *)
From iris.bi.lib Require Import fractional.
Local Open Scope Z_scope.

Require Export WpGprCsrrCommon WpGprCsrrA WpGprCsrrB.

(* Shared base for the S-mode per-decode-family leaf files (WpSmode<Family>.v).
   Holds the shared kernel-window instruction tactics and re-exports the M-mode
   leaf base. Primitives are Require Import (local, non-propagating) to avoid
   changing notation resolution in downstream files. *)
Require Import SailStdpp.Operators_mwords Riscv.rv64d_types Riscv.rv64d SailStdpp.Base.
Require Import RiscvLang RiscvPtsto.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language.
From stdpp Require Import bitvector.definitions gmap.

Require Import SmodeCore.
From Kernel Require Import KernelInstrs KernelSyms.
From Stdlib Require Import Lia List.
From iris.program_logic Require Import lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
From iris.bi.lib Require Import fractional.
Require Import Riscv.riscv_extras SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d.
Import Defs.
Local Open Scope Z_scope.


(* ---- Generic gpr-write engine lemmas (internal plumbing for the per-instruction
   specific leaf lemmas in the WpSmode<Family>.v files). Relocated here from the
   former WpSmodeToBeDeleted.v so callers use the specific per-instruction lemmas. *)
Section WpSmodeGprEngine.
  Context `{!riscvGS Σ, !sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.







End WpSmodeGprEngine.

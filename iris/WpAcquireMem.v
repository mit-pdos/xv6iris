(* WpAcquireMem.v -- the 8-byte register-base store [c.sd rs2', uimm(rs1')]
   S-mode WP (acquire()'s [sd a0,16(s1)] writing lk->cpu).  Cloned from
   WpPushOffMem.wp_csw_s with the access width changed 4 -> 8, on the
   register-generic 8-byte STORE execute lemmas of WpSmodeGpr. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Export WpSmodeLoad WpSmodeStore WpSmodeBtype.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Section WpAcquireMem.
  Context `{!riscvGS Σ}.
  Context `{CID : CpuId}.



  (* ------------------------------------------------------------------ *)
  (* [_ram] variants of the 8-byte S-mode load/store: the whole Sv39     *)
  (* super-page-identity geometry is DERIVED internally from the owned    *)
  (* [pa ↦₈ _] (which carries [addr_is_ram]), so the caller supplies NO   *)
  (* geometry.  Placed here (rather than in the downstream WpFreelistMem) *)
  (* so every S-mode WP -- holding/acquire/release/kalloc/kfree -- can    *)
  (* reach them by handing over just the points-to.                       *)
  (* ------------------------------------------------------------------ *)


End WpAcquireMem.

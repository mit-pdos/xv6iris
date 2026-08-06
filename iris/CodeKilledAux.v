(* CodeKilledAux.v -- the machine code of killed(): the decode
   templates for the words this function alone uses, and the [instr]
   constructors for its instruction addresses.  Consumed by ProofKilled.v. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpMmodeLeafBase.
Require Import KernelText.
Require Import KernelRvcDecode WpRvcBridge WpDecodeBridge.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeKilled.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation kl_ra := (mword_of_int 1 : mword 5).

Section CodeKilledAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

(* ---- the two decodes not already shared ---- *)
(* +0x12  0x549c  c.lw a5,40(s1)  -- p->killed *)

(* +0x0e  0xab9fe0ef  jal ra,acquire  (0x80002150 -> 0x80000c08 = -5448) *)

(* +0x18  0xb37fe0ef  jal ra,release  (0x8000215a -> 0x80000c90 = -5322) *)

End CodeKilledAux.

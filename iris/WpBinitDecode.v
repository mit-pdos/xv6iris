(* WpBinitDecode.v *)
From Stdlib Require Import ZArith.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes WpDecodeBridge WpRvcBridge.
Require Import KernelText.
Require Import WpMmodeLeafBase.
Require Import KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
Local Open Scope Z_scope.
Import Defs.

Lemma bidb_45848493 s : register_lookup misa (sregs s) = MISA_C -> cfg_ok s -> exec (ext_decode (mword_of_int 0x45848493 : mword 32)) s = Some (ITYPE (mword_of_int 1112 : mword 12, Regidx (mword_of_int 9), Regidx (mword_of_int 9), ADDI), s). Proof. decode_bridge_ms. Qed.

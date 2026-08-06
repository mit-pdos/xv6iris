(* CodeSetkilledAux.v -- the machine code of setkilled(): the decode templates
   for the words this function alone uses, and the [instr] constructors for
   its instruction addresses.  Consumed by ProofSetkilled.v.

     +0x00  1101      c.addi     sp,sp,-32
     +0x02  ec06      c.sdsp     ra,24(sp)
     +0x04  e822      c.sdsp     s0,16(sp)
     +0x06  e426      c.sdsp     s1,8(sp)
     +0x08  1000      c.addi4spn s0,sp,32
     +0x0a  84aa      c.mv       s1,a0        park [p] across the two calls
     +0x0c  adffe0ef  jal        ra,acquire
     +0x10  4785      c.li       a5,1
     +0x12  d49c      c.sw       a5,40(s1)    p->killed = 1
     +0x14  8526      c.mv       a0,s1
     +0x16  b5dfe0ef  jal        ra,release
     +0x1a  60e2      c.ldsp     ra,24(sp)
     +0x1c  6442      c.ldsp     s0,16(sp)
     +0x1e  64a2      c.ldsp     s1,8(sp)
     +0x20  6105      c.addi16sp sp,32
     +0x22  8082      c.ret

   Slot 0 of the 32-byte frame is padding: setkilled saves three registers,
   not four (killed's fourth slot holds s2, the value it parks across
   release -- a void function has nothing to park). *)
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
Require Import KernelRvcDecode WpDecodeBridge.
From Kernel Require KernelInstrs KernelSyms.
Require Import CodeSetkilled.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.
Local Open Scope Z_scope.

Notation sk_ra := (mword_of_int 1 : mword 5).

(* [cdec_d49c] / [cexec_d49c] -- the [c.sw a5,40(s1)] -- live in
   KernelRvcDecode.v: kkill stores the same word at the same offset. *)

Section CodeSetkilledAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  (* +0x0c  0xadffe0ef  jal ra,acquire  (0x8000212a -> 0x80000c08 = -5410) *)

  (* +0x16  0xb5dfe0ef  jal ra,release  (0x80002134 -> 0x80000c90 = -5284) *)

End CodeSetkilledAux.

(* CodeProcPagetableAux.v -- decode catalog for xv6's proc_pagetable()
   (kernel/proc.c).  KernelInstrs.v bytes at KernelSyms.proc_pagetable
   (0x80001a0e ..): the 4-slot frame (addi sp,-32; ra/s0/s1/s2 saves), the
   uvmcreate jal + null test, the TRAMPOLINE mappages group (li a4,10;
   auipc/addi a3 -> trampoline; lui a2,0x1; lui/addi/slli a1 -> TRAMPOLINE;
   jal mappages; bltz), the TRAPFRAME group (li a4,6; ld a3,88(s2); ...;
   jal mappages; bltz) and the shared epilogue at +0x4c.

   The catalog covers the SUCCESS path only (+0x00 .. +0x58): the two
   error tails (+0x5a uvmfree, +0x66 uvmunmap/uvmfree) are CATALOGUED (they
   are reachable in the uncounted regime kfork needs; unreachable
   under the proof's page budget, so no instruction there is ever fetched.

   Same architecture as CodeKvmmake.v; JAL residues = (target-pc) mod 2^21. *)
From Stdlib Require Import ZArith.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes KernelText.
Require Import WpDecode WpDecodeBridge WpRvcBridge.
Require Import WpMmodeLeafBase.
From Kernel Require KernelSyms.
Require Import KernelBaseDecode.
Require Import KernelRvcDecode.
Require Import CodeProcPagetable.
Import Defs.

Section ProcPagetableInstrs.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Notation PPT off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.proc_pagetable + off) : mword 64) rvc ast).

  (* ---- instr lemmas ---- *)

  (* ---- the two FAILURE TAILS' own base words (the three call targets) ---- *)

  (* 0x5e  jal uvmfree   (offset -0x69a) *)

  (* 0x74  jal uvmunmap  (offset -0x884) *)

  (* 0x7c  jal uvmfree   (offset -0x6b8) *)

  (* ---- the tails' [instr] facts.  Tail #1 (+0x5a .. +0x64) is the FIRST
     mappages failure: uvmfree(pagetable, 0), return 0.  Tail #2 (+0x66 ..
     +0x82) is the second: drop the trampoline it had just mapped, then
     uvmfree, then return 0.  Both join the shared epilogue at +0x4c. ---- *)

End ProcPagetableInstrs.

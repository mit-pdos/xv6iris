(* CodeKvmmakeAux.v -- the machine code of xv6's kvmmake() (kernel/vm.c): the
   per-instruction decode facts and [instr] constructors at KernelSyms.kvmmake
   (0x8000110e .. 0x800011bc, 64 instrs) -- the 4-slot frame (addi sp,-32;
   ra/s0/s1 saves), the root kalloc jal, the memset jal, the six
   {lui/auipc/addi arg setup + kvmmap jal} region groups, and the
   proc_mapstacks jal.  JAL residues = (target - pc) mod 2^21; immediates/ASTs
   are the exact vm_compute-on-decode outputs.  kvminit's code is in
   CodeKvminit.v. *)
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
Require Import CodeKvmmake.
Import Defs.

Section CodeKvmmakeAux.
  Context `{!riscvGS Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

  Local Notation KMK off rvc ast :=
    (kernel_text -∗ instr (mword_of_int (KernelSyms.kvmmake + off) : mword 64) rvc ast).

  (* ---- kvmmake instr lemmas ---- *)

End CodeKvmmakeAux.

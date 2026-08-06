(* CodeSwtchAux.v -- the machine code of swtch: the decode templates and the
   [instr] constructors for its instruction addresses.  Split out of WpSwtchVc.v,
   which keeps the weakest preconditions over them. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExec RiscvFetchExec.
Require Import InstrBytes.
Require Import WpDecode KernelText.
Require Import WpMmodeLeafBase.
Require Import WpRvcBridge.
Require Import SmodeCore KernelRvcDecode.
From Kernel Require KernelInstrs.
From Kernel Require KernelSyms.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import WpDecodeBridge.
Require Import CodeSwtch.
Local Open Scope Z_scope.
Import Defs.

Section CodeSwtchAux.
  Context `{!riscvGS Σ}.
  Context `{!sieG Σ}.
  Context `{GEN : GenId} `{CID : CpuId}.

(* ---- base sd rs2,off(a0) : STORE (off, rs2, a0, 8) ---- *)

(* ---- base ld rd,off(a1) : LOAD (off, a1, rd, false, 8) ---- *)

(* ---- compressed c.sd/c.ld decode facts ---- *)

(* creg / immediate reconciliations for the clean ExecuteAs expansions *)

(* ---- clean ExecuteAs expansions for the four compressed instructions ---- *)

(* the three instr-builder templates, copied verbatim from CodeMycpu/CodeKalloc *)
(* ------ the 28 instr facts of swtch's straight-line body ------ *)

(* +0x68 c.ret : jalr x0,0(x1) *)
Lemma swi_ret : kernel_text -∗ instr (mword_of_int (KernelSyms.swtch + 0x68) : mword 64) true
    (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)).
Proof. mk_rvc (KernelSyms.swtch + 0x68)%Z (mword_of_int 0x8082 : mword 16)
  (mword_of_int (KernelSyms.swtch + 0x68) : mword 64)
  (JALR (zeros' 12, Regidx (mword_of_int 1), zreg)) cdec_8082 exec_execute_C_JR. Qed.

End CodeSwtchAux.

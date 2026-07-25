(* SpecMyproc.v -- the public interface of Myproc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   THE current-process contract: myproc() returns exactly the process the
   current-process resource says is assigned to this CPU ([cur_proc p],
   ProcGeom.v -- ownership of cpus[cpuid].proc holding p), reading the cell
   under push_off/pop_off.  The hart id is the ambient CpuId: the spec pins
   tp = [cid_word].

   (SpecWakeup.v's [wp_myproc_sconf_any] axiom is the older, weaker ∃-j
   interface used by wakeup, which threads no current-process resource.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation MP := KernelSyms.myproc.

Definition wp_myproc_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.myproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (* the hart id is the ambient CpuId *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ pc_is pcE -∗
  ( ∀ (ms : mword 64) (mf : regfile),
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ n eb p C -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = p ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MYPROC.
  Parameter wp_myproc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_myproc_sconf_body γ Φ m av n eb p C.
End MYPROC.

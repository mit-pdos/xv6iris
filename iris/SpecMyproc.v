(* SpecMyproc.v -- the public interface of Myproc, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   THE current-process contract: myproc() returns exactly the process the
   current-process resource says is assigned to this CPU ([cur_proc p],
   ProcGeom.v -- ownership of cpus[cpuid].proc holding p), reading the cell
   under push_off/pop_off.  The hart id is the ambient CpuId: the spec pins
   tp = [cid_word].

   This is the only myproc interface: wakeup threads [cur_proc] and uses it
   directly, so there is no current-process-free ∃-j variant anywhere. *)
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
Require Import WpNext.
Require Import CpuOwn.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation MP := KernelSyms.myproc.

(* myproc() does its OWN push_off/pop_off around the [tp]-read inside
   mycpu() (only ITS interior runs at [b = false]):

     myproc(void) { push_off(); struct cpu *c = mycpu();
                    struct proc *p = c->proc; pop_off(); return p; }

   so the whole-function contract stays [b]-GENERIC: [p], the value it
   returns, is the process ASSIGNED to this cpu -- a THREAD-dependent
   quantity, not a hart-dependent one.  A migration mid-call changes which
   hart resumes, but not which process cpus[cid].proc names once resumed
   (the resource is re-established at the new hart by push_off/mycpu/pop_off
   run there), so nothing here needs [b = false].  Contrast [cpuid()]/
   [mycpu()] itself, whose returned hart id a migration WOULD invalidate. *)
Definition wp_myproc_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.myproc in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (* push_off's transient noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (10 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own n eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (ms : mword 64) (mf : regfile),
      ⌜ sconf_ms_facts ms ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own n eb p C b -∗
      pc_is ret_tgt -∗
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = p ⌝ -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MYPROC.
  Parameter wp_myproc_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (b : bool),
      wp_myproc_sconf_body Φ m av n eb p C b.
End MYPROC.

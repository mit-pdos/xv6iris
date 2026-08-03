(* SpecUserinit.v -- the public interface of userinit() (kernel/proc.c), stated
   as an ASSUMED contract.  There is no [ProofUserinit.v]: this is the
   [Module Type] + [Axiom]-in-the-Link shape
   (claude-notes/design/spec-modules.md, "An ASSUMED callee"), and
   [LinkUserinit.v] supplies the only instance.

     void userinit(void) {
       struct proc *p = allocproc();
       initproc = p;
       uvmfirst(p->pagetable, initcode, sizeof(initcode));
       p->sz = PGSIZE;
       p->trapframe->epc = 0;
       p->trapframe->sp = PGSIZE;
       safestrcpy(p->name, "initcode", sizeof(p->name));
       p->cwd = namei("/");
       p->state = RUNNABLE;
       release(&p->lock);
     }

   WHY ASSUMED, DELIBERATELY.  userinit's callee [namei] drags in the whole
   file-system cone (iget / ilock / readi / dirlookup / the log), which is far
   from anything proven.  main() is the only caller and needs SOME contract to
   be a functor over; assuming this one keeps [ProofMain.v] axiom-free and
   makes proving userinit later a change to exactly two files -- this one and
   its [Axiom].

   THE INTERFACE IS THE WEAKEST THING main() CAN PAY.  Nothing about the first
   process crosses back out: main does not use [initproc], and the process
   userinit made is reached by the scheduler through [procs_inv], which is
   persistent and rides in unchanged.  So the post is the frame plus the
   resources that went in, and the only cell that genuinely moves is the
   [initproc] global -- in at an arbitrary value, out at an unspecified one.

   THE TWO NUMERIC CONSTANTS ARE PROVISIONAL.  [K_userinit] and
   [userinit_pages] are budgets nobody has measured: [namei]'s real stack
   depth is unknown and allocproc's page appetite is only bounded by reading
   the source.  They are set to what main() has available and to a
   comfortable over-estimate respectively.  Adjusting them when the real proof
   is attempted replaces this file plus the [Axiom] in [LinkUserinit.v] and
   nothing else. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import RegFile InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpNext.
Require Import WpLock.
Require Import CpuOwn.
Require Import FdSlots.
Require Import SchedCtx.
Require Import KallocInv KvmSpec.
Require Import SpecPanic.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation UI := KernelSyms.userinit.

(* PROVISIONAL stack budget: 50 is what main() has available below its own
   two-slot frame ([SpecMain.K_main] = 52).  namei's real depth is unknown. *)
Definition K_userinit : nat := 50%nat.

(* PROVISIONAL kalloc budget: allocproc takes one page for the trapframe and
   one for the process's page-table root, uvmfirst one more for the first user
   page plus up to two interior nodes, and namei's cone allocates nothing.
   Eight leaves slack. *)
Definition userinit_pages : nat := 8%nat.

Definition wp_userinit_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (Φ : mval -> iProp Σ) (γs : list gname)
    (m0 : regfile) (K : nat)
    (eb : bool) (pj : mword 64) (C : iProp Σ)
    (on : option nat) (v0 : mword 64) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.userinit in
  let ra_idx : mword 5 := mword_of_int 1 in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (K_userinit <= K)%nat ->
  (* enough pages for allocproc's trapframe + page table and uvmfirst's first
     user page; stated exactly as virtio_disk_init states its three *)
  (exists nb, on = Some nb /\ (userinit_pages <= nb)%nat) ->
  sie_cap_gpr m0 K b pj -∗
  (* [kernel_data] supplies the "initcode" / "/" string literals *)
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  panic_wp_any -∗
  cpu_own 0%nat eb pj C b -∗
  (* the proc array's lock invariant: allocproc scans it, and release gives
     back the slot userinit found.  Persistent, so threading it is free. *)
  procs_inv Φ γs -∗
  kalloc_env γa on -∗
  (* the one global cell userinit writes *)
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v0 -∗
  wp_next b pj (fun (CID : CpuId) =>
  ∀ mf : regfile,
    sie_cap_gpr mf K b pj -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 mf /\ mf !!! Regidx ra_idx = ra0 ⌝ -∗
    cpu_own 0%nat eb pj C b -∗
    kalloc_env γa (avail_sub on userinit_pages) -∗
    (∃ v : mword 64, (mword_of_int KernelSyms.initproc : mword 64) ↦₈ v) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type USERINIT.
  Parameter wp_userinit_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !kallocG Σ, !fdslotG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (Φ : mval -> iProp Σ) (γs : list gname)
      (m0 : regfile) (K : nat)
      (eb : bool) (pj : mword 64) (C : iProp Σ)
      (on : option nat) (v0 : mword 64) (b : bool),
      wp_userinit_sconf_body γa Φ γs m0 K eb pj C on v0 b.
End USERINIT.

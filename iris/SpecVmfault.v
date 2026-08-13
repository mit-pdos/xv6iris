(* SpecVmfault.v -- the public interface of Vmfault, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

   vmfault(pagetable, psz, va, read) is the lazy-allocation page-fault
   handler: below [psz] and unmapped, it kallocs a page, zeroes it, and maps
   it PTE_W|PTE_U|PTE_R at PGROUNDDOWN(va); anything else returns 0.

   *** IT NO LONGER CONFLATES THE TABLE IT IS GIVEN WITH THE RUNNING
   PROCESS'S. ***  xv6 `4f2fc8b` made both halves of the old conflation go
   away: the size arrives as an ARGUMENT instead of being read from
   `myproc()->sz`, and the [mappages] goes into [pagetable] rather than
   `myproc()->pagetable`.  vmfault now touches NEITHER proc cell, so this
   contract takes neither -- [p_sz p ↦₈{dqs} szv] and
   [p_pagetable p ↦₈{dqp} …] are gone, and with them the [dqs]/[dqp]
   parameters.  [szv] is simply the a1 register value.

   THAT IS THE FIRST OF kexec's THREE UPSTREAM BLOCKERS, RETIRED
   (claude-notes/projects/kexec.md).  copyout's contract had to assume its
   destination table WAS the running process's, because the vmfault beneath it
   mapped into `p->pagetable` whatever table it was handed.  kexec cannot
   satisfy that: it copies the argv strings into the NEW table while still
   running on the old one.  With vmfault honest about which table it maps
   into, copyout can be stated over an arbitrary [proc_pt P], and kexec can
   use it.

   THE CONTRACT IS STATED AT THE [proc_pt] ALTITUDE: vmfault PRESERVES the
   valid-user-page-table predicate of the table it operates on.  On failure
   the caller gets [proc_pt P] back unchanged (the tree may have grown
   interior nodes -- invisible, [pt_frame] is existential); on success it
   gets [proc_pt (uptd_insert P (svpn_of va0) r)]: the SAME predicate with
   the user map grown by exactly one entry -- the kalloc page [r] as a
   user-RW leaf -- whose well-formedness ([proc_pt_wf]: upt_map_wf,
   upt_acc_wf, um_pages_valid) is re-established inside, and whose page
   ownership has moved from kalloc's [page_own] into [proc_pt_own].

   The new page's ZEROED contents are deliberately not exposed: [proc_pt]
   owns pages at existential bytes (the user-safety altitude).

   Steady-state kalloc tier: [kalloc_env γa None is persistent (sealed
   count witness), so it is taken once and not returned; kalloc may fail
   nondeterministically, which is folded into the failure arm.

   [uint szv <= 2^38] is the one fact the caller must know about p->sz
   (MAXVA); where the canonical sz well-formedness lives is settled by the
   usertrap/sbrk work (see claude-notes/completed/vmfault.md). *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var ghost_map.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvPtsto RiscvLang RiscvExtras.
Require Import SmodeCore.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import RegFile HartTp WpNext.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import KallocInv.
Require Import KvmSpec.
Require Import UserPtTree.
Require Import ProcPtOwn.
From Kernel Require KernelSyms.


Definition wp_vmfault_sconf_body `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
    (γa : gname) (mm : regfile)
    (P : uptd) (szv : mword 64) (K lvl : nat) (eb : bool) (p : mword 64)
    (C : iProp Σ) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.vmfault in
  (* a0 = pagetable, a1 = psz, a2 = va, a3 = read *)
  let va := mm !!! Regidx (mword_of_int 12) in
  let va0 : mword 64 := and_vec va (mword_of_int (-4096)) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1)) in
  (38 <= K)%nat ->
  (* the kalloc/mappages chain runs on the ambient CPU (push_off cid
     convention) *)
  mm !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the pagetable argument is the table [proc_pt P] describes -- and that is
     now the WHOLE requirement.  It used to have to be [p->pagetable] as well,
     because the mappages went there regardless; it does not any more. *)
  mm !!! Regidx (mword_of_int 10) = page_base P.(ud_root) ->
  (* the size argument, in a1 *)
  mm !!! Regidx (mword_of_int 11) = szv ->
  (* it respects MAXVA *)
  (uint szv <= 2 ^ 38)%Z ->
  (* kalloc's acquire keeps the transient noff increment in int range;
     [lvl] is otherwise generic -- vmfault runs at whatever nesting its
     caller holds (usertrap at 0, pipewrite/piperead's copies at 1) *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  cpu_own lvl eb p C b -∗
  kernel_text -∗
  pc_is pcE -∗
  proc_pt P -∗
  kalloc_env γa None -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile),
    sie_cap_gpr mr K b p -∗
    cpu_own lvl eb p C b -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    ( (⌜mr !!! Regidx (mword_of_int 10) = mword_of_int 0⌝ ∗ proc_pt P)
      ∨ (∃ r : mword 64,
           ⌜mr !!! Regidx (mword_of_int 10) = r⌝ ∗
           ⌜page_valid r⌝ ∗
           ⌜(uint va < uint szv)%Z⌝ ∗
           ⌜P.(ud_um) !! svpn_of va0 = None⌝ ∗
           proc_pt (uptd_insert P (svpn_of va0) r)) ) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type VMFAULT.
  Parameter wp_vmfault_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !sieG Σ, !kallocG Σ} `{GEN : GenId} `{CID : CpuId}
      (γa : gname) (mm : regfile)
      (P : uptd) (szv : mword 64) (K lvl : nat) (eb : bool) (p : mword 64)
      (C : iProp Σ) (b : bool),
      wp_vmfault_sconf_body γa mm P szv K lvl eb p C b.
End VMFAULT.

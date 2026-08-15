(* SpecSysOpenStub.v -- a placeholder contract for sys_open(), which has NO
   Iris proof anywhere in the tree yet (claude-notes/projects/fs-sysfile.md
   tracks it as outstanding, alongside create/dirlink/sys_unlink).
   syscall()'s dispatch table reaches it at index 15
   (KernelSyms.sys_open), so ProofSyscall.v's dispatch needs SOME contract
   to apply at that arm -- this is it.

   Mirrors LinkKerneltrap.v's idiom (claude-notes/design/spec-modules.md,
   "An ASSUMED callee: Module Type + an Axiom in the link"): the STATEMENT
   lives here, honestly, as a Module Type; LinkSysOpenStub.v supplies it with
   an [Axiom] -- visible to [Print Assumptions] and to
   [tools/proof_coverage.py]'s textual scan, unlike a bare [Declare Module].

   THE SHAPE IS wp_syscall_sconf_body ITSELF (SpecSyscall.v), entry point
   changed.  From syscall()'s point of view sys_open is just ANOTHER arm of
   the dispatch, so rather than inventing a weaker ad hoc contract, the
   honest thing to assume is exactly what a REAL proof of this function
   would eventually have to deliver: the same R/bn/fn/us/ip/dqi vocabulary
   [SpecSyscall.wp_syscall_sconf_body] threads to every other arm, in and
   out, at [KernelSyms.sys_open] instead of [KernelSyms.syscall].  This
   keeps a future real proof a drop-in replacement: whatever discharges
   [SYSOPEN] plugs into [ProofSyscall.v]'s functor unchanged. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FdSlots.
Require Import FileInvDefs.
Require Import UserPtTree.
Require Import ProcInv.
Require Import SchedCtx.
Require Import IrefSlots.
Require Import PanicStub.
Require Import BioInv.
Require Import SpecFileclose.
Require Import KallocInv.
Require Import DiskPtsto DiskInv.
Require Import WpUart.
Require Import FsBlocks LogInv.
Require Import FsCrash.
Require Import InodeRegion.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import ProcAvail.
Local Open Scope Z_scope.
Import Defs.

(* No real budget to state -- this is an assumed callee, not a proved one --
   so a small constant that the dispatch's own arithmetic can always meet. *)
Definition K_sys_open : nat := 4%nat.

Definition wp_sys_open_sconf_body
    `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
      !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
      !irefslotG Σ, !pavG Σ, !iregG Σ}
    `{GEN : GenId} `{CID : CpuId}
    (R : gname -> mword 64 -> iProp Σ)
    (γf : gname) (γs : list gname) (j : nat) (γl : gname)
    (bn : bio_names) (fn : fclose_names) (us : gset Z)
    (ip : mword 64) (dqi : dfrac)
    (m : regfile) (av : nat)
    (pid : mword 32) (V : pprivate) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.sys_open in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (j < NPROC)%nat ->
  γs !! j = Some γl ->
  (K_sys_open <= av)%nat ->
  sie_cap_gpr m av true pj -∗
  cpu_own 0%nat true pj true lks -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  procs_inv γs -∗
  panic_wp_any -∗
  bslots bn 3 -∗
  fileclose_bm fn us -∗
  (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
  fd_slots FDSPARE -∗
  iref_slots IREFSPARE -∗
  R γf pj -∗
  proc_priv γf pj pid V -∗
  wp_next true pj (fun (CID : CpuId) =>
    ∀ (mf : regfile) (V' : pprivate) (us' : gset Z),
      ⌜ callee_saved m mf ⌝ -∗
      ⌜ ud_tfp (pv_upt V') = ud_tfp (pv_upt V) ⌝ -∗
      sie_cap_gpr mf av true pj -∗
      cpu_own 0%nat true pj true lks -∗
      bslots bn 3 -∗
      fileclose_bm fn us' -∗
      (mword_of_int KernelSyms.initproc : mword 64) ↦₈{dqi} ip -∗
      fd_slots FDSPARE -∗
      iref_slots IREFSPARE -∗
      R γf pj -∗
      proc_priv γf pj pid V' -∗
      pc_is ret_tgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type SYSOPEN.
  Parameter wp_sys_open_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ, !fileG Σ, !kallocG Σ,
             !bioG Σ, !diskGhostG Σ, !uartGhostG Σ, !fsLogG Σ, !logG Σ, !fsCrashG Σ,
             !irefslotG Σ, !pavG Σ, !iregG Σ}
      `{GEN : GenId} `{CID : CpuId}
      (R : gname -> mword 64 -> iProp Σ)
      (γf : gname) (γs : list gname) (j : nat) (γl : gname)
      (bn : bio_names) (fn : fclose_names) (us : gset Z)
      (ip : mword 64) (dqi : dfrac)
      (m : regfile) (av : nat)
      (pid : mword 32) (V : pprivate) (lks : gset string),
      wp_sys_open_sconf_body R γf γs j γl bn fn us ip dqi m av pid V lks.
End SYSOPEN.

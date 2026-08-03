(* SpecAcquiresleep.v -- the public interface of Acquiresleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The separation-logic lock spec, sleeplock flavour:

     { is_sleeplock γl γ slk s R ∗ <thread resources> }
       acquiresleep(slk)
     { sleeplocked γ ∗ sl_pid slk ↦₄ pid ∗ R ∗ <thread resources> }

   The <thread resources> are what the body's callees demand: the per-cpu
   push_off cells and the inner lock's cpu word (acquire/release), the
   current-process resource and the caller's own pid cell at a read
   fraction (lk->pid = myproc()->pid), and -- because the wait loop parks
   through sleep() -- the running-thread bundle of the scheduler protocol
   (SpecSleep.v).  Entered with no spinlocks held (intr_count 0, noff cell
   0): sleep() requires exactly one level outstanding, which forces it. *)
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
Require Import HartTp WpNext.
Require Import WpLock.
Require Import SpecPanic.
Require Import FdSlots.
Require Import ProcGeom.
Require Export SwtchCtx.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import SwtchCtx.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation ASL := KernelSyms.acquiresleep.

Definition wp_acquiresleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (j < NPROC)%nat ->
  (26 <= av)%nat ->
  (* PARKING PREMISE (hart-generic scheduler protocol): the saved base enable
     is [true].  Everything below sleeps, and a parking thread must hand the
     trap CSRs across the crossing -- at level 0 with an enabled base the
     pushing acquire produces exactly that set.  See SpecSched.v. *)
  eb = true ->
  sie_cap_gpr m av b pj -∗
  cpu_own 0 eb pj C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  panic_wp_any -∗
  (* the caller's own pid (read-only fraction) *)
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through to sleep() *)
  procs_inv Φ γs -∗
  scheds_inv Φ γs -∗
  own_ctx (p_context pj) -∗
  park_hlf j true -∗
  wp_next b pj (fun (CID : CpuId) =>
    ∀ (mf : regfile),
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr mf av b pj -∗
      cpu_own 0 eb pj C b -∗
      pc_is ret_tgt -∗
      (* the lock is now HELD: token + pid field + protected resource *)
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      p_pid pj ↦₄{dq} pidv -∗
      own_ctx (p_context pj) -∗
      park_hlf j true -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ACQUIRESLEEP.
  Parameter wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fdslotG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac} (b : bool),
      wp_acquiresleep_sconf_body Φ γs j γl γsl s R m pidv av eb C dq b.
End ACQUIRESLEEP.

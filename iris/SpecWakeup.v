(* SpecWakeup.v -- the public interface of wakeup (the whole function), stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import SmodeCore.
Require Import FdSlots.
Require Import ProcGeom.
Require Import InstrBytes KernelText.
Require Import WpLock.
Require Import PanicStub.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved.
Require Import IntrDefs HartTp WpNext.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import SchedCtx.
From Kernel Require KernelSyms.

(* THE SCAN NO LONGER SKIPS THE RUNNING PROCESS.  xv6's wakeup used to guard
   the whole body with [if (p != myproc())]; it now acquires every slot's
   lock, including its own, and clears [p->chan] wherever it matches --
   because the field is the wakeup FLAG the split sleep protocol
   (SpecSleep.v) reads, so a registered-but-not-yet-parked waiter has to be
   signalled too, and the caller may BE that waiter.

   Two premises went with the guard: the [myproc()] call is gone from the
   code, so [a0f] (&cpus[tp], the value it returned) and the [a0f <> 0]
   refutation have nothing left to name.  Reaching one's own slot needs no
   new resource -- p->lock hands out only the invariant's HALF of the state
   mirror, and the running thread's own half stays where it is; the write
   arm is licensed by the state READ being SLEEPING, which is unclaimed, so
   the proof never has to know which slot is the caller's. *)
Definition wp_wakeup_sconf_body `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
     (m : regfile) (γs : list gname) (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (18 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  (* acquire's push_off keeps the transient noff increment in range *)
  (Z.of_nat lvl + 1 < 2 ^ 31)%Z ->
  sie_cap_gpr m K b pme -∗
  cpu_own lvl eb pme C b -∗
  kernel_text -∗ pc_is (mword_of_int KernelSyms.wakeup) -∗
  panic_wp_any -∗ procs_inv γs -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ Mf : regfile,
      ⌜ callee_saved m Mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap Mf)) ⌝ -∗
      sie_cap_gpr Mf K b pme -∗
      cpu_own lvl eb pme C b -∗
      kernel_text -∗ pc_is rettgt -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type WAKEUP.
  Parameter wp_wakeup_sconf :
    forall `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !irefslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
       (m : regfile) (γs : list gname) (pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_wakeup_sconf_body m γs pme lvl K eb C b.
End WAKEUP.

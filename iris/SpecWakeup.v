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
Require Import SpecPanic.
Require Import WpMmodeLeafBase.
Require Import CalleeSaved.
Require Import IntrDefs HartTp WpNext.
Require Import CpuOwn.
Require Import ProcGeom.
Require Import SchedCtx.
From Kernel Require KernelSyms.

Definition wp_wakeup_sconf_body `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
     (m : regfile) (γs : list gname) (a0f pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool) :=
  let sp0 : mword 64 := m !!! Regidx csp_rs1 in
  let spF := add_vec sp0 (sign_extend' 64 (caddi16sp_imm (mword_of_int 60 : mword 6))) in
  let rettgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (18 <= K)%nat ->
  (forall r : regidx, r ∈ dom (rf_to_gmap m)) ->
  length γs = NPROC ->
  mycpu_ret (rget m Rtp) = a0f ->
  eq_vec (zero_reg : mword 64) (mycpu_ret (rget m Rtp)) = false ->
  (* myproc/acquire's push_off keeps the transient noff increment in range *)
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
    forall `{!riscvGS Σ, !lockG Σ, !fdslotG Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
       (m : regfile) (γs : list gname) (a0f pme : mword 64) (lvl K : nat) (eb : bool) (C : iProp Σ) (b : bool),
      wp_wakeup_sconf_body m γs a0f pme lvl K eb C b.
End WAKEUP.

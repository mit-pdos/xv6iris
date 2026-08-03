(* SpecHoldingsleep.v -- the public interface of Holdingsleep, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   The HOLDER's variant (the only one xv6 uses -- every call site asserts
   the lock is held): with the token, the pid field the holder carries, and
   the caller's own pid cell agreeing on the value, holdingsleep returns 1.

     { is_sleeplock γl γ slk s R ∗ sleeplocked γ ∗ sl_pid slk ↦₄ pidv
       ∗ cur_proc p ∗ p_pid p ↦₄{dq} pidv ∗ <cells> }
       holdingsleep(slk)
     { a0 = 1 ∗ (everything back) }

   The v = 0 arm inside the inner critical section is refuted by token
   exclusivity ([sl_res_open_held]); the pid comparison closes from the
   agreement of the two pid resources.  Calls myproc().  (tp holds this hart's id by construction now --
   HartTp.tp_pin -- so no contract states it.) *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SpecPanic.
Require Import ProcGeom.
Require Import CpuOwn.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation HSL := KernelSyms.holdingsleep.

Definition wp_holdingsleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) (dq : dfrac) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holdingsleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (16 <= av)%nat ->
  sie_cap_gpr m av b p -∗
  cpu_own 0 eb p C b -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle (returned untouched) *)
  sleeplocked γsl -∗
  sl_pid slk ↦₄ pidv -∗
  panic_wp_any -∗
  (* the caller's own pid, agreeing with the lock's pid field *)
  p_pid p ↦₄{dq} pidv -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
      sie_cap_gpr mf av b p -∗
      cpu_own 0 eb p C b -∗
      pc_is ret_tgt -∗
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      p_pid p ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type HOLDINGSLEEP.
  Parameter wp_holdingsleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (eb : bool) (C : iProp Σ) {dq : dfrac} (b : bool),
      wp_holdingsleep_sconf_body Φ γl γsl s R m p pidv av eb C dq b.
End HOLDINGSLEEP.

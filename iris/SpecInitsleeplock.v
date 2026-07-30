(* SpecInitsleeplock.v -- the public interface of Initsleeplock, stated
   independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be
   checked in parallel.

   initsleeplock(lk, name) = initlock(&lk->lk, "sleep lock") + zeroing the
   locked/pid fields + storing the name pointer.  Like initlock, it returns
   the RAW zeroed cells plus the two persistent names; the caller seals them
   into [is_sleeplock] with [new_sleeplock] (SleepLock.v), supplying the
   resource R the new lock is to protect. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import RegFile HartTp WpNext.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation ISL := KernelSyms.initsleeplock.

(* the "sleep lock" string literal in rodata (the auipc/addi pair at
   ISL+0x10 resolves here); the caller extracts the persistent [↦ₛ□] from
   [kernel_data] via [kernel_data_string]. *)
Definition sl_str_addr : mword 64 := mword_of_int 0x80007548.

Definition wp_initsleeplock_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ)
    (m : regfile) (s : string)
    (vlocked vlk vpid : mword 32) (vlkname vcpu vname : mword 64)
    (av : nat) (b : bool) :=
  let pcE : mword 64 := mword_of_int KernelSyms.initsleeplock in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let name := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))
                   in
  (6 <= av)%nat ->
  sie_cap_gpr m av b -∗
  kernel_text -∗ pc_is pcE -∗
  (* the two strings: the fixed "sleep lock" literal for the inner spinlock,
     and the caller's own name for the sleeplock (both duplicable). *)
  sl_str_addr ↦ₛ□ "sleep lock"%string -∗
  name ↦ₛ□ s -∗
  (* the six struct fields, raw *)
  slk ↦₄ vlocked -∗
  sl_lk slk ↦₄ vlk -∗
  lock_name_field (sl_lk slk) ↦₈ vlkname -∗
  sl_lkcpu slk ↦₈ vcpu -∗
  sl_name_field slk ↦₈ vname -∗
  sl_pid slk ↦₄ vpid -∗
  wp_next b (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr av b -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    slk ↦₄ (mword_of_int 0 : mword 32) -∗
    sl_lk slk ↦₄ (mword_of_int 0 : mword 32) -∗
    (* both name fields are written once and DISCARDED: what comes back are
       the persistent [lock_name]/[sl_name], ready for [new_sleeplock]. *)
    lock_name (sl_lk slk) "sleep lock"%string -∗
    sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
    sl_name slk s -∗
    sl_pid slk ↦₄ (mword_of_int 0 : mword 32) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type INITSLEEPLOCK.
  Parameter wp_initsleeplock_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ)
      (m : regfile) (s : string)
      (vlocked vlk vpid : mword 32) (vlkname vcpu vname : mword 64)
      (av : nat) (b : bool),
      wp_initsleeplock_sconf_body Φ m s vlocked vlk vpid vlkname vcpu vname av b.
End INITSLEEPLOCK.

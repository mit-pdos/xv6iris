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
   agreement of the two pid resources.  Calls myproc(), so tp = cid_word. *)
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
Require Import KptTree.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation HSL := KernelSyms.holdingsleep.

Definition wp_holdingsleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) (dq : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holdingsleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* the hart id is the ambient CpuId *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (16 <= av)%nat ->
  sconf γ -∗
  hart_state ↦ᵣ HART_ACTIVE tt -∗
  sie_cap_gpr γ root_ppn m av -∗
  intr_count γ root_ppn 0 -∗
  tlb_inv_pt root_ppn -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  (* the holder's bundle (returned untouched) *)
  sleeplocked γsl -∗
  sl_pid slk ↦₄ pidv -∗
  sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
  a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  (* the current process and its pid, agreeing with the lock's pid field *)
  cur_proc p -∗
  p_pid p ↦₄{dq} pidv -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
      sconf γ -∗
      hart_state ↦ᵣ HART_ACTIVE tt -∗
      sie_cap_gpr γ root_ppn mf av -∗
      intr_count γ root_ppn 0 -∗
      tlb_inv_pt root_ppn -∗
      pc_is ret_tgt -∗
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      cur_proc p -∗
      p_pid p ↦₄{dq} pidv -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type HOLDINGSLEEP.
  Parameter wp_holdingsleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (root_ppn : mword 44) (Φ : mval -> iProp Σ)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (p : mword 64) (pidv : mword 32) (av : nat) {dq : dfrac},
      wp_holdingsleep_sconf_body γ root_ppn Φ γl γsl s R m p pidv av dq.
End HOLDINGSLEEP.

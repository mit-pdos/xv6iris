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
Require Import WpLock.
Require Import ProcGeom.
Require Import SchedCtx.
Require Import SpecSched.
Require Import SleepLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation ASL := KernelSyms.acquiresleep.

Definition wp_acquiresleep_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (γs : list gname) (j : nat)
    (γl γsl : gname) (s : string) (R : iProp Σ)
    (m : regfile) (pidv : mword 32) (av : nat) (dq : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.acquiresleep in
  let slk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let pj := proc_addr j in
  let ret_tgt := update_vec_dec (add_vec (m !!! Regidx (mword_of_int 1 : mword 5))
                   (sign_extend' 64 (zeros' 12))) 0 ('b"0") in
  (* the hart id is the ambient CpuId *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (j < NPROC)%nat ->
  eq_vec (access_vec_dec ret_tgt 0) ('b"0") = true ->
  (26 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  intr_count γ 0 -∗
  kernel_text -∗ pc_is pcE -∗
  is_sleeplock γl γsl slk s R -∗
  sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
  a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
  (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
  (* the current process and its pid (read-only fraction) *)
  cur_proc pj -∗
  p_pid pj ↦₄{dq} pidv -∗
  (* the running-thread bundle threaded through to sleep() *)
  p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
  procs_inv γ Φ γs -∗
  own_ctx (p_context pj) -∗
  ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf ⌝ -∗
      sie_cap_gpr γ mf av -∗
      intr_count γ 0 -∗
      pc_is ret_tgt -∗
      (* the lock is now HELD: token + pid field + protected resource *)
      sleeplocked γsl -∗
      sl_pid slk ↦₄ pidv -∗
      R -∗
      sl_lkcpu slk ↦₈ (zero_reg : mword 64) -∗
      a_cpu_noff cid_word ↦₄ (mword_of_int 0 : mword 32) -∗
      (∃ iv : mword 32, a_cpu_int cid_word ↦₄ iv) -∗
      cur_proc pj -∗
      p_pid pj ↦₄{dq} pidv -∗
      p_lkcpu pj ↦₈ (zero_reg : mword 64) -∗
      own_ctx (p_context pj) -∗
      ▷ sched_vc γ Φ γs (a_cpu_ctx cid_word) -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ACQUIRESLEEP.
  Parameter wp_acquiresleep_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (γs : list gname) (j : nat)
      (γl γsl : gname) (s : string) (R : iProp Σ)
      (m : regfile) (pidv : mword 32) (av : nat) {dq : dfrac},
      wp_acquiresleep_sconf_body γ Φ γs j γl γsl s R m pidv av dq.
End ACQUIRESLEEP.

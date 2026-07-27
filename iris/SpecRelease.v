(* SpecRelease.v -- the public interface of Release, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   The [locked γl cpu_id] token is the whole precondition on the lock side: it
   says this hart holds the lock AND pins [lk->cpu] at this hart's [struct cpu]
   (which is what makes release's own [holding(lk)] check return 1).  Both lock
   words live in the invariant, so no cell is threaded.

   THREE statements, ONE proof.  Release's last store to the lock word is the
   moment -- the only moment -- at which the lock's storage can change hands:
   the state ghost is back at [None] and the two words and [R] are all in hand
   together, so whether the invariant closes again or is destroyed has to be
   decided right there.  [wp_release_gen_sconf_body] takes that decision as a
   parameter (a [lock_finisher], WpLock.v) and hands its output [Out] back to
   the caller; [RELEASE] and [RELEASE_CANCEL] below are its two instances:

     RELEASE         -- the static kernel lock: no credential, no disposal,
                        nothing comes back out.  Verbatim what the thirteen
                        ordinary consumers were written against.
     RELEASE_CANCEL  -- the kalloc'd object's lock, over [cinv]: surrender
                        every share and release RECLAIMS the lock's own two
                        words along with [R], which is what lets pipeclose
                        [kfree] the page. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants cancelable_invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import MinstretInv.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import ProcGeom CpuOwn.
Require Import WpLock.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation RL := KernelSyms.release.

(* The generic form.  [Tc] is the right to touch the lock at all -- presented
   on the way in, threaded through holding()'s two reads and the [lk->cpu]
   clear, and finally handed to the finisher, which spends it (or does not) as
   it likes.  The finisher's mask is the step engine's [⊤ ∖ ↑minstretN]: the
   choice is made INSIDE the atomic store, so no other hart can see the window
   in which the lock is free but its storage already spoken for. *)
Definition wp_release_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R Tc Dc Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (* the tp register holds THIS cpu's id (pop_off's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lka R Tc Dc -∗
  Tc -∗
  locked γl cpu_id -∗
  R -∗
  lock_finisher γl lka R Tc Dc Out (⊤ ∖ ↑minstretN) -∗
  cpu_own γ (S n) eb p C -∗
  trap_csrs_pay n eb -∗
  ( ∀ mr,
    Out -∗
    sie_cap_gpr γ mr av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own γ n eb p C -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_release_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (* the tp register holds THIS cpu's id (pop_off's cid convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  locked γl cpu_id -∗
  R -∗
  cpu_own γ (S n) eb p C -∗
  trap_csrs_pay n eb -∗
  ( ∀ mr,
    sie_cap_gpr γ mr av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own γ n eb p C -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* The cancelling instance, stated directly over the [cinv] flavour so a
   caller never has to build a finisher: bring every share of the cancel
   token and release gives back the lock's own two words along with [R] --
   the whole object, ready to be reassembled into a page and freed.  The
   invariant is GONE afterwards, so [cinv] does not reappear in the post. *)
Definition wp_release_cancel_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !cinvG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl γc : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (10 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  kernel_text -∗ pc_is pcE -∗
  cinv lockN γc (lock_inv γl lka R) -∗
  cinv_own γc 1 -∗
  locked γl cpu_id -∗
  R -∗
  cpu_own γ (S n) eb p C -∗
  trap_csrs_pay n eb -∗
  ( ∀ mr,
    lka ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lka ↦₈ (zero_reg : mword 64) -∗
    R -∗
    sie_cap_gpr γ mr av -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own γ n eb p C -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASE_GEN.
  Parameter wp_release_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R Tc Dc Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_gen_sconf_body γ Φ γl lka R Tc Dc Out m n eb p C av.
End RELEASE_GEN.

Module Type RELEASE.
  Parameter wp_release_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_sconf_body γ Φ γl lka s R m n eb p C av.
End RELEASE.

Module Type RELEASE_CANCEL.
  Parameter wp_release_cancel_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !cinvG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl γc : gname) (lka : mword 64) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_cancel_sconf_body γ Φ γl γc lka R m n eb p C av.
End RELEASE_CANCEL.

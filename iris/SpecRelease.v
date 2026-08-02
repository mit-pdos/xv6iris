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
     RELEASE_CANCEL  -- the kalloc'd object's lock: release RECLAIMS the
                        lock's own two words along with whatever the caller
                        makes of [R], which is what lets pipeclose [kfree]
                        the page. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile HartTp WpNext.
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

(* The generic form.  release opens the lock invariant at four instructions
   and presents, at each, the very token it is already holding -- [locked] for
   the first three and [locked_pre] for the word clear.  That is not a
   convenience: by the time release runs, the object's last REFERENCE has
   necessarily gone home, and the lock is all its closer has left.  So what
   the caller owes is a refutation of the dead state [Dc] from each token.

   The finisher's mask is the step engine's [⊤ ∖ ↑minstretN]: the choice is
   made INSIDE the atomic store, so no other hart can see the window in which
   the lock is free but its storage already spoken for. *)
Definition wp_release_gen_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R Dc Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the arm on the way OUT: at n = 0 the level fully unwinds, so pop_off's
     re-enable flip fires and the live SIE mode becomes exactly the saved
     base [eb]; at any deeper n it stays disabled -- see
     [CpuOwn.cpu_own]/[IntrDefs.intr_count]/[intr_count_dec], which pins the
     ghost eighth at '0' unconditionally for every [S _] level. *)
  let outb := match n with O => eb | S _ => false end in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (10 <= av)%nat ->
  (⊢ locked γl cpu_id -∗ Dc -∗ False) ->
  (⊢ locked_pre γl cpu_id -∗ Dc -∗ False) ->
  (* holding the lock forces the level to be at least 1, hence interrupts
     disabled on entry -- this is not a choice, it is what [cpu_own (S n)]
     already means *)
  sie_cap_gpr m av false p -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lka R Dc -∗
  locked γl cpu_id -∗
  R -∗
  lock_finisher γl lka R Dc Out (⊤ ∖ ↑minstretN) -∗
  cpu_own (S n) eb p C false -∗
  trap_csrs_pay n eb -∗
  wp_next outb p (fun (CID : CpuId) =>
    ∀ mr,
    Out -∗
    sie_cap_gpr mr av outb p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own n eb p C outb -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_release_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* see [wp_release_gen_sconf_body] for why this is the exit arm *)
  let outb := match n with O => eb | S _ => false end in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (10 <= av)%nat ->
  sie_cap_gpr m av false p -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  locked γl cpu_id -∗
  R -∗
  cpu_own (S n) eb p C false -∗
  trap_csrs_pay n eb -∗
  wp_next outb p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr av outb p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own n eb p C outb -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

(* The cancelling instance: release DESTROYS the lock at its word clear and
   walks off with the storage.  The caller brings the dead state [D] it wants
   the invariant to degenerate into, refutations of it from the two holder
   tokens, and a wand that BUILDS [D] out of the lock's own spent state
   fragment plus whatever it finds in [R].

   That indirection is not decoration: for a multiply-owned object the last
   closer has necessarily already surrendered part of the certificate INTO
   [R] (the other end closed before it did), and [R] must be handed in intact
   because release's word clear reassembles the invariant on the branch it
   does not take.  So the certificate can only be completed inside the
   finisher, with [R] in hand.  See PipeInv.pipe_res_dead. *)
Definition wp_release_cancel_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R D Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.release in
  let lk0 := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* see [wp_release_gen_sconf_body] for why this is the exit arm *)
  let outb := match n with O => eb | S _ => false end in
  add_vec lk0 (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (10 <= av)%nat ->
  (⊢ locked γl cpu_id -∗ D -∗ False) ->
  (⊢ locked_pre γl cpu_id -∗ D -∗ False) ->
  sie_cap_gpr m av false p -∗
  kernel_text -∗ pc_is pcE -∗
  lock_openable γl lka R D -∗
  locked γl cpu_id -∗
  R -∗
  (* the licence to destroy, cashed inside the store *)
  (lock_frag γl None -∗ R ==∗ D ∗ Out) -∗
  cpu_own (S n) eb p C false -∗
  trap_csrs_pay n eb -∗
  wp_next outb p (fun (CID : CpuId) =>
    ∀ mr,
    lka ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_cpu lka ↦₈ (zero_reg : mword 64) -∗
    Out -∗
    sie_cap_gpr mr av outb p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    cpu_own n eb p C outb -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type RELEASE_GEN.
  Parameter wp_release_gen_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R Dc Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_gen_sconf_body Φ γl lka R Dc Out m n eb p C av.
End RELEASE_GEN.

Module Type RELEASE.
  Parameter wp_release_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_sconf_body Φ γl lka s R m n eb p C av.
End RELEASE.

Module Type RELEASE_CANCEL.
  Parameter wp_release_cancel_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (R D Out : iProp Σ) (m : regfile) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) (av : nat),
      wp_release_cancel_sconf_body Φ γl lka R D Out m n eb p C av.
End RELEASE_CANCEL.

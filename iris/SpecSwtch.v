(* SpecSwtch.v -- the public interface of Swtch, stated independently of its
   proof.  Requires only the definitional layer (SwtchCtx.v) -- never a
   whole-function proof file -- so every function proof can be checked in
   parallel.

   swtch(old,new) with the coroutine-chain protocol: consume the ▷-guarded
   [valid_context γ Φ P newc] (▷ because a scheduler can only ever RE-store a
   parked context under ▷ -- its own swtch delivered it that way) plus the
   chain payload [P newc oldc tp]; the machine ends up running new's saved
   WP.  The interface is FULL-BUNDLE on both sides: the caller hands
   [sie_cap_gpr γ m0 av] and [cpu_own γ 1 eb p emp] whole, and its
   continuation (the content of [valid_context γ Φ P oldc]) receives, on a
   later resumption, [sie_cap_gpr γ m av] at a fresh file [m] with its own
   saved image and its own [av], plus [cpu_own γ 1 eb' p emp] at its own
   [p] and the resumer's [eb'], and the chain hand-off [▷ valid_context γ Φ P cret ∗ P oldc cret tp']
   (tp' = the resumer's x4, how the resumed code re-ties its per-CPU cells
   to its own tp). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import SmodeCore.
Require Import IntrDefs CpuOwn.
Require Import SwtchCtx.
From Kernel Require KernelSyms.
Import Defs.

Notation SW := KernelSyms.swtch.

Definition wp_swtch_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (P : mword 64 -d> mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
    (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64))
    (av : nat) (eb : bool) (p : mword 64) :=
  length old_vs = 14%nat ->
  m0 !!! Regidx (mword_of_int 10 : mword 5) = oldc ->
  m0 !!! Regidx (mword_of_int 11 : mword 5) = newc ->
  kernel_text -∗
  (* THE FULL AMBIENT BUNDLES, both directions: the suspender hands its
     whole [sie_cap_gpr] (stack + avail included -- they park in ITS
     [valid_context] record, keyed by the saved sp) and its [cpu_own] at
     level 1 (xv6's noff==1-at-swtch invariant; slot [emp] -- the context
     cells travel as [ctx_cells]); on a later resumption its continuation
     receives the SAME shapes back: its own [av] (sp is callee-saved, the
     stack re-attaches), a fresh file with its saved image, and the
     [cpu_own γ 1 eb' p emp] back at the SAME [p] (the record parks it;
     the protocol's c->proc pre-set makes the resumer's bundle match) and
     the RESUMER's [eb'] -- swtch stores nothing to struct cpu, so the
     same-eb contract is realized one level up by sched's own epilogue
     intena store + ghost retune. *)
  sie_cap_gpr γ m0 av -∗
  cpu_own γ 1 eb p emp -∗
  pc_is (mword_of_int KernelSyms.swtch) -∗
  ctx_cells oldc old_vs -∗
  ▷ valid_context γ Φ P newc p -∗
  P newc oldc (m0 !!! Regidx (mword_of_int 4 : mword 5)) p -∗
  ( ∀ (m : regfile) (eb' : bool),
      ⌜callee_img m = callee_img m0⌝ -∗
      sie_cap_gpr γ m av -∗
      cpu_own γ 1 eb' p emp -∗
      pc_is (ret_pc (m !!! Regidx (mword_of_int 1 : mword 5))) -∗
      ctx_cells oldc (callee_img m0) -∗
      (∃ cret : mword 64,
         ▷ valid_context γ Φ P cret p ∗
         P oldc cret (m !!! Regidx (mword_of_int 4 : mword 5)) p) -∗
      WP (Loop : expr riscv_lang) {{ Φ }} ) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type SWTCH.
  Parameter wp_swtch_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (P : mword 64 -d> mword 64 -d> mword 64 -d> mword 64 -d> iPropO Σ)
      (oldc newc : mword 64) (m0 : regfile) (old_vs : list (mword 64))
      (av : nat) (eb : bool) (p : mword 64),
      wp_swtch_sconf_body γ Φ P oldc newc m0 old_vs av eb p.
End SWTCH.

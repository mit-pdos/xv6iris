(* SpecPushOff.v -- the public interface of PushOff, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
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
Require Import ProcGeom SwtchCtx CpuOwn.
Require Import WpIntenaBits WpMycpu.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation PO := KernelSyms.push_off.
Notation PP := KernelSyms.pop_off.

Definition wp_push_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :=
  (* push_off's mstatus0-dependent register chain N2..N8 + storeval32 (which
     read [sstatus_read mstatus0]) are reconstructed inside the proof over the
     unbundled mstatus0; the statement stays mstatus0-free.  The noff/intena
     cells and the counting token ride inside [cpu_own]: the noff cell IS the
     level [n], the intena cell records [eb] once n ≥ 1, so no cell arguments
     and no level-mirror premises appear here. *)
  let caller_ret := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the tp register holds THIS cpu's id (the chain-wide convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the noff increment stays in int range *)
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (6 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ pc_is (mword_of_int (KernelSyms.push_off + 0x00) : mword 64) -∗
  ( ∀ (ms : mword 64) (mfin : regfile),
    ⌜ sconf_ms_facts ms ⌝ -∗
    sie_cap_gpr γ mfin av -∗
    cpu_own γ (S n) eb p C -∗
    trap_csrs_pay n eb -∗
    pc_is caller_ret -∗
    ⌜ callee_saved m mfin ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_pop_off_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
    (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ) :=
  let pcE : mword 64 := mword_of_int KernelSyms.pop_off in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* both panic checks (intr_get(), noff < 1) and the noff-1 == 0 branch are
     facts of [cpu_own]: the level is S n > 0, SIE is pinned '0' by the count
     eighth, and the final pop's re-enable branch reads intena = [eb]. *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (4 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ (S n) eb p C -∗
  trap_csrs_pay n eb -∗
  kernel_text -∗ pc_is pcE -∗
  ( ∀ mf,
    sie_cap_gpr γ mf av -∗
    cpu_own γ n eb p C -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mf ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PUSHOFF.
  Parameter wp_push_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_push_off_sconf_body γ Φ m av n eb p C.
  Parameter wp_pop_off_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (m : regfile) (av : nat)
      (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ),
      wp_pop_off_sconf_body γ Φ m av n eb p C.
End PUSHOFF.

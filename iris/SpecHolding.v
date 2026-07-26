(* SpecHolding.v -- the public interface of Holding, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel.

   holding(lk) reads BOTH of the lock's words, and both belong to the lock
   invariant (WpLock.v), so the caller passes no [lk->cpu] cell.  Two forms:

     - with no evidence, the answer is unknown: 0 or 1 (a non-holder cannot
       see the owner word, so this is all that is true).  acquire calls
       holding() this way and absorbs the 1 answer with panic's contract.
     - with the [locked] holder token, the answer is provably 1 (the token
       pins [lk->cpu] at this hart's [struct cpu]); the token comes back out.
       That is release's check. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import IntrDefs.
Require Import WpLock.
Require Import WpMycpu.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation HD := KernelSyms.holding.

Definition wp_holding_lockinv_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  (* the tp register holds THIS cpu's id (the mycpu convention) *)
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (6 <= n)%nat ->
  sie_cap_gpr γ m n -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  ( ∀ mh,
    sie_cap_gpr γ mh n -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      (mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 0 : mword 64) \/
       mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64)) ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Definition wp_holding_lockinv_locked_s_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat) :=
  let pcE : mword 64 := mword_of_int KernelSyms.holding in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  add_vec lk (sign_extend' 64 (mword_of_int 0 : mword 12)) = lka ->
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (6 <= n)%nat ->
  sie_cap_gpr γ m n -∗
  kernel_text -∗ pc_is pcE -∗
  is_lock γl lka s R -∗
  locked γl cpu_id -∗
  ( ∀ mh,
    sie_cap_gpr γ mh n -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mh /\
      mh !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int 1 : mword 64) ⌝ -∗
    locked γl cpu_id -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type HOLDING.
  Parameter wp_holding_lockinv_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat),
      wp_holding_lockinv_s_sconf_body γ Φ γl lka s R m n.
  Parameter wp_holding_lockinv_locked_s_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ) (γl : gname) (lka : mword 64) (s : string) (R : iProp Σ) (m : regfile) (n : nat),
      wp_holding_lockinv_locked_s_sconf_body γ Φ γl lka s R m n.
End HOLDING.

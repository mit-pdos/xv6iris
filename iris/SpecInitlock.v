(* SpecInitlock.v -- the public interface of Initlock, stated independently of its
   proof.  Requires only the definitional layer -- never a whole-function proof
   file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText.
Require Import IntrDefs.
Require Import IntrDefs WpNext.
Require Import WpLock.
Require Import RegFile.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.


Definition wp_initlock_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (vlock : bv 32) (vname vcpu : bv 64) (s : string) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.initlock in
  let lk := m !!! Regidx (mword_of_int 10 : mword 5) in
  let name := m !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 0x10 : mword 12)) in
  (2 <= K)%nat ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ pc_is pcE -∗
  (* the string argument [a1] points at: DUPLICABLE (persistent) ownership,
     so the caller keeps its copy and initlock can seal it into the lock. *)
  name ↦ₛ□ s -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    (* the name field comes back OWNED, holding the string pointer initlock
       wrote.  It is inside the object's storage -- for a kalloc'd object,
       inside the page [kfree] memsets -- so handing back the persistent
       [lock_name] instead would make that storage unreclaimable.  A caller
       whose lock is static seals it with [lock_name_intro] and forgets it;
       one that will free the object keeps it. *)
    c_name ↦₈ name -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type INITLOCK.
  Parameter wp_initlock_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{GEN : GenId} `{CID : CpuId} (m : regfile) (vlock : bv 32) (vname vcpu : bv 64) (s : string) (K : nat) (b : bool) (p : mword 64),
      wp_initlock_sconf_body m vlock vname vcpu s K b p.
End INITLOCK.

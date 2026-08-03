(* SpecPrintkinit.v -- the public interface of Printkinit, stated independently
   of its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel. *)
From Stdlib Require Import Eqdep_dec ZArith Lia List.
From stdpp Require Import gmap list list_monad bitvector.definitions bitvector.tactics.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import ghost_var gen_heap invariants.
From iris.program_logic Require Import language weakestpre lifting.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import RegFile WpNext.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Notation PK := KernelSyms.printkinit.

(* The address of the string literal "pr" that printkinit passes as initlock's
   [name] argument.  It sits in .rodata just past etext and has no ELF symbol of
   its own, so it is spelled out here (see kernel.asm: 80007028 <etext+0x28>). *)
Definition pr_name_str : Z := 0x80007028%Z.

(* printkinit() = initlock(&pr.lock, "pr").  It takes no arguments and touches
   no state beyond the three fields of the global [pr.lock]: the caller hands
   the word and the cpu field in raw and gets them back zeroed, and the name
   field comes back sealed as the persistent [lock_name lk "pr"].  Whether the
   lock then becomes an [is_lock] over some printk resource is the caller's
   ghost step, not printkinit's -- it need only add the invariant
   ([is_lock_intro]).  The "pr" literal itself is read out of [kernel_data]. *)
Definition wp_printkinit_sconf_body `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.printkinit in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5) : mword 64) in
  let lk : mword 64 := mword_of_int KernelSyms.pr in
  let c_name := lock_name_field lk in
  let c_cpu := add_vec lk (sign_extend' 64 (mword_of_int 16 : mword 12)) in
  (4 <= K)%nat ->
  sie_cap_gpr m K b p -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  lk ↦₄ vlock -∗
  c_name ↦₈ vname -∗
  c_cpu ↦₈ vcpu -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mr ⌝ -∗
    lk ↦₄ (mword_of_int 0 : mword 32) -∗
    lock_name lk "pr"%string -∗
    c_cpu ↦₈ (zero_reg : mword 64) -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type PRINTKINIT.
  Parameter wp_printkinit_sconf :
    forall `{!riscvGS Σ} `{!sieG Σ} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (m : regfile) (K : nat) (vlock : bv 32) (vname vcpu : bv 64) (b : bool) (p : mword 64),
      wp_printkinit_sconf_body Φ m K vlock vname vcpu b p.
End PRINTKINIT.

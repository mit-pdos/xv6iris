(* SpecMycpu.v -- the public interface of Mycpu, stated independently of its
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
Require Import RegFile InstrBytes HartTp.
Require Import SmodeCore.
Require Import CalleeSaved KernelText.
Require Import IntrDefs.
Require Import ProcGeom.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

  (* INTERRUPTS MUST BE DISABLED -- xv6 says so in as many words above
     mycpu() ("Interrupts must be disabled"), and the explicit-cpuid refactor
     turns that comment into a premise.  The [tp] read happens MID-function, so
     with interrupts enabled a migration before it would have the instruction
     read the RESUMING hart's tp: the returned id would be neither the entry
     hart's nor the exit hart's, and no [let] outside the continuation can name
     it.  At [b = false] no trap is taken, the hart cannot move, and the id is
     the entry hart's -- so the contract is stated at [false] and needs no
     [wp_next] at all (it would collapse by [wp_next_off] anyway). *)
Definition wp_mycpu_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m0 : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let tp_idx : mword 5 := mword_of_int 4 in
  let a0_idx : mword 5 := mword_of_int 10 in
  let pcE := mword_of_int KernelSyms.mycpu in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  sie_cap_gpr kt m0 n false p -∗
  kernel_text -∗ pc_is pcE -∗
  ( ∀ m' : regfile,
    sie_cap_gpr kt m' n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m0 m' /\
      m' !!! Regidx a0_idx = mycpu_ret (rget m0 tp_idx) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

  (* INTERRUPTS MUST BE DISABLED -- xv6 says so in as many words above
     mycpu() ("Interrupts must be disabled"), and the explicit-cpuid refactor
     turns that comment into a premise.  The [tp] read happens MID-function, so
     with interrupts enabled a migration before it would have the instruction
     read the RESUMING hart's tp: the returned id would be neither the entry
     hart's nor the exit hart's, and no [let] outside the continuation can name
     it.  At [b = false] no trap is taken, the hart cannot move, and the id is
     the entry hart's -- so the contract is stated at [false] and needs no
     [wp_next] at all (it would collapse by [wp_next_off] anyway). *)
Definition wp_call_mycpu_sconf_cs_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (p : mword 64) :=
  let ra_idx : mword 5 := mword_of_int 1 in
  let m0 := <[Regidx (mword_of_int 1 : mword 5) := regval_into_reg (add_vec_int P 4)]> m in
  let pcE := mword_of_int KernelSyms.mycpu in
  let ra0 := m0 !!! Regidx ra_idx in
  let ret_tgt := ret_pc ra0 in
  add_vec P (sign_extend' 64 jimm) = pcE ->
  eq_vec (access_vec_dec (pcE : mword 64) 0) ('b"0") = true ->
  (2 <= n)%nat ->
  sie_cap_gpr kt m n false p -∗
  kernel_text -∗ pc_is P -∗
  instr P false (JAL (jimm, Regidx (mword_of_int 1 : mword 5))) -∗
  ( ∀ mo,
    sie_cap_gpr kt mo n false p -∗
    pc_is ret_tgt -∗
    ⌜ callee_saved m mo /\
      mo !!! Regidx (mword_of_int 10 : mword 5)
        = mycpu_ret (rget m (mword_of_int 4 : mword 5)) ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type MYCPU.
  Parameter wp_mycpu_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (m0 : regfile) (n : nat) (p : mword 64),
      wp_mycpu_sconf_body kt m0 n p.
  Parameter wp_call_mycpu_sconf_cs :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (kt : ktier) (P : mword 64) (jimm : mword 21) (m : regfile) (n : nat) (p : mword 64),
      wp_call_mycpu_sconf_cs_body kt P jimm m n p.
End MYCPU.

(* SpecArgraw.v -- the public interface of argraw(), stated independently of
   its proof.

     static uint64 argraw(int n) {
       struct proc *p = myproc();
       switch (n) {
       case 0: return p->trapframe->a0;
       ...
       case 5: return p->trapframe->a5;
       }
       panic("argraw");
       return -1;
     }

   @ KernelSyms.argraw = 0x8000271a, 30 instructions.  gcc compiles the
   switch to a JUMP TABLE: the six 4-byte self-relative offsets at
   0x80007758 (.rodata, inside [kernel_data]) are indexed by n, added to the
   table base, and entered with an indirect [c.jr a5].  So this is the first
   proof in the tree over a computed indirect jump -- see ProofArgraw.v.

   THE CONTRACT.  The index is given as a nat [i < NARG] with the register
   pinned at [mword_of_int i]: that PRECONDITION is what refutes the
   [bltu a5,s1,panic] arm, so argraw needs no [panic_wp] hypothesis at all.
   The resources are the weakest that suffice, deliberately NOT [proc_priv]:

     - [p_trapframe p ↦₈{dqt} page_base tfp] -- a fraction of the pointer
       cell, which [ProcInv.proc_priv_trapframe] hands out;
     - [tf_page tfp ws] -- the WHOLE trapframe page (all 36 struct words with
       their values, plus the tail).  The nth argument is word
       [tf_arg_idx n = 14 + n], which is exactly the imm field argraw's
       [c.ld a0,<112+8n>(a5)] encodes.

   Threading the whole [proc_priv] instead would drag [fileG]/[γf] into the
   syscall-argument path purely to follow a pointer.  Same judgement as for
   [p_pid] in SpecAcquiresleep / SpecHoldingsleep. *)
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
Require Import CalleeSaved KernelText KernelDataInv.
Require Import IntrDefs.
Require Import WpLock.
Require Import ProcGeom CpuOwn.
Require Import FileInv ProcInv.
Require Import UserPtTree ProcPtOwn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation AR := KernelSyms.argraw.

Definition wp_argraw_sconf_body `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
    (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
    (dqt : dfrac) :=
  let pcE : mword 64 := mword_of_int KernelSyms.argraw in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  m !!! Regidx (mword_of_int 4 : mword 5) = cid_word ->
  (* the switch index, in range: this is what refutes the panic arm *)
  (i < NARG)%nat ->
  m !!! Regidx (mword_of_int 10 : mword 5) = mword_of_int (Z.of_nat i) ->
  ws !! tf_arg_idx i = Some v ->
  (Z.of_nat n + 1 < 2 ^ 31)%Z ->
  (* 4 slots for this frame, 10 for myproc's *)
  (14 <= av)%nat ->
  sie_cap_gpr γ m av -∗
  cpu_own γ n eb p C -∗
  kernel_text -∗ kernel_data -∗ pc_is pcE -∗
  p_trapframe p ↦₈{dqt} page_base tfp -∗
  tf_page tfp ws -∗
  ( ∀ mf : regfile,
      ⌜ callee_saved m mf /\
        mf !!! Regidx (mword_of_int 10 : mword 5) = v ⌝ -∗
      sie_cap_gpr γ mf av -∗
      cpu_own γ n eb p C -∗
      pc_is ret_tgt -∗
      p_trapframe p ↦₈{dqt} page_base tfp -∗
      tf_page tfp ws -∗
      WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type ARGRAW.
  Parameter wp_argraw_sconf :
    forall `{!riscvGS Σ, !sieG Σ, !lockG Σ, !fileG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (m : regfile) (av : nat) (n : nat) (eb : bool) (p : mword 64) (C : iProp Σ)
      (i : nat) (tfp : mword 44) (ws : list (mword 64)) (v : mword 64)
      (dqt : dfrac),
      wp_argraw_sconf_body γ Φ m av n eb p C i tfp ws v dqt.
End ARGRAW.

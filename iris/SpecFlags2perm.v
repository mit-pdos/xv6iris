(* SpecFlags2perm.v -- the public interface of flags2perm() (kernel/exec.c),
   stated independently of its proof.  Requires only the definitional layer --
   never a whole-function proof file -- so every function proof can be checked
   in parallel.

     int flags2perm(int flags) {
       int perm = 0;
       if (flags & 0x1) perm = PTE_X;
       if (flags & 0x2) perm |= PTE_W;
       return perm;
     }

   @ KernelSyms.flags2perm = 0x8000469c, 16 instructions / 32 bytes; a 2-slot
   ra/s0 frame and no callees, so [K = 2] and there is no [cpu_own].

   THE MACHINE COMPUTES A DIFFERENT EXPRESSION FROM THE C, and the contract
   states the machine's:

     mv    a5,a0
     slliw a0,a0,0x3      a0 = sext32(flags << 3)
     andi  a0,a0,8        a0 = 8 * bit0(flags)         <- the [flags & 1] test
     andi  a5,a5,2
     beqz  a5,+0x18
     ori   a0,a0,4        a0 |= 4                      <- the [flags & 2] test

   gcc turned the first branch into a SHIFT-AND-MASK: bit 0 of [flags] is
   moved into bit 3 and every other bit is masked off, so no [beqz] is emitted
   for it and the value is [8 * bit0].  Only the second test survives as a
   branch.  Both readings agree ([PTE_X = 8], [PTE_W = 4]), but only the
   machine's is what the proof steps through, and only the machine's makes the
   answer a function of two BITS rather than of a comparison.

   [f2p] is therefore stated on the bits, and the fact its one caller needs is
   [f2p_cases]: the answer is one of four literals.  kexec hands the result
   straight to uvmalloc as its [xperm], and uvmalloc asks for
   [0 <= xperm < 512] and [uvm_perm_ok (Z.lor xperm 18)] -- the four instances
   [ProcPtOwn.uvm_perm_ok_18 / _22 / _26 / _30] being exactly [Z.lor _ 18] at
   these four values.  That is why the contract does NOT mention
   [uvm_perm_ok]: keeping ProcPtOwn out of a leaf spec whose function knows
   nothing about page tables is worth the one case split at the call site.

   THE ARGUMENT IS A C [int] AND THE RESULT IS READ AS ONE, but neither shows
   in the contract: [slliw]'s sign extension only ever reaches bits at or
   above 3, and both [andi]s clear those, so the answer depends on bits 0 and
   1 of a0 alone and no range premise on [flags] is needed. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvLang RiscvPtsto RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


(* flags2perm's own 2-slot frame; it calls nothing. *)
Notation K_flags2perm := (2%nat) (only parsing).
(* THE ANSWER, as a function of the two bits the machine actually inspects. *)
Definition f2p (fl : mword 64) : Z :=
  (if Z.testbit (bv_unsigned fl) 0 then 8 else 0)
  + (if Z.testbit (bv_unsigned fl) 1 then 4 else 0).

(* What every caller uses: the four literals.  [uvmalloc]'s [0 <= xperm < 512]
   and [uvm_perm_ok (Z.lor xperm 18)] both follow by [vm_compute] on each. *)
Lemma f2p_cases (fl : mword 64) :
  f2p fl = 0 \/ f2p fl = 4 \/ f2p fl = 8 \/ f2p fl = 12.
Proof.
  unfold f2p.
  destruct (Z.testbit (bv_unsigned fl) 0), (Z.testbit (bv_unsigned fl) 1); lia.
Qed.

Lemma f2p_range (fl : mword 64) : 0 <= f2p fl < 512.
Proof. destruct (f2p_cases fl) as [-> | [-> | [-> | ->]]]; lia. Qed.

Definition wp_flags2perm_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (kt : ktier) (mm : regfile) (K : nat) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.flags2perm in
  let fl := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (K_flags2perm <= K)%nat ->
  sie_cap_gpr kt mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    sie_cap_gpr kt mr K b p -∗
    pc_is ret_tgt -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜mr !!! Regidx (mword_of_int 10 : mword 5)
       = (mword_of_int (f2p fl) : mword 64)⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type FLAGS2PERM.
  Parameter wp_flags2perm_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (kt : ktier) (mm : regfile) (K : nat) (b : bool) (p : mword 64),
      wp_flags2perm_sconf_body kt mm K b p.
End FLAGS2PERM.

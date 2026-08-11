(* SpecMemcmp.v -- the public interface of memcmp(), stated independently of
   its proof.

     int memcmp(const void *v1, const void *v2, uint n)

   @ KernelSyms.memcmp, 58 bytes; a 2-slot ra/s0 frame; calls nothing.

   memcmp walks the two buffers in lockstep.  If some index [k < n] has
   [v1[k] != v2[k]], it stops at the FIRST such [k] and returns the difference
   of the two bytes read as UNSIGNED chars -- the code is

       lbu a5,0(a0) ; lbu a4,0(a1) ; bne a5,a4 ; ... ; subw a0,a5,a4

   so both operands are zero-extended bytes and the result is the 32-bit
   difference sign-extended into a0.  Since both bytes lie in [0,256), that
   32-bit difference is exactly [v1[k] - v2[k]] over Z, which is what
   [memcmp_res] states via [mword_of_int (bv_unsigned (f k) - bv_unsigned (g k))]
   -- the same return-value vocabulary SpecStrncmp.v already uses.  If no such
   [k] exists (including the [n = 0] case, which the source's [c.beqz a2] arm
   short-circuits), it returns 0.

   ALIASING IS ALLOWED, and that is why the two buffers arrive under SEPARATE
   DFRACS [dq1]/[dq2] rather than as two full-ownership conjuncts: memcmp only
   READS, so a caller comparing a buffer against itself (or two overlapping
   windows of one object) must be able to satisfy the precondition, and two
   fractional [↦ₘ{#q}] over the same address are simultaneously ownable
   whenever [q1 + q2 <= 1].  This is exactly where memcmp differs from
   SpecMemmove.v, whose full-ownership conjuncts ARE its non-overlap
   hypothesis; memcmp needs no non-overlap at all.

   Requires only the definitional layer -- never a whole-function proof file --
   so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang RiscvExtras.
Require Import InstrBytes KernelText.
Require Import RegFile WpNext.
Require Import SmodeCore.
Require Import CalleeSaved.
Require Import IntrDefs.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.

(* The value memcmp leaves in a0: either the unsigned-byte difference at the
   first differing index, or 0 when the two windows agree on all [n] bytes. *)
Definition memcmp_res (f g : nat -> bv 8) (n : nat) (res : mword 64) : Prop :=
  (exists k, (k < n)%nat /\
     (forall j, (j < k)%nat -> f j = g j) /\
     f k <> g k /\
     res = (mword_of_int (bv_unsigned (f k) - bv_unsigned (g k)) : mword 64))
  \/ ((forall j, (j < n)%nat -> f j = g j) /\ res = (mword_of_int 0 : mword 64)).

Definition wp_memcmp_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
    (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.memcmp in
  let s1 := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let s2 := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the 2-slot frame; memcmp calls nothing *)
  (2 <= K)%nat ->
  mm !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 32)%Z ->
  sie_cap_gpr mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ{dq1} f j) -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ{dq2} g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s1 j) ↦ₘ{dq1} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s2 j) ↦ₘ{dq2} g j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜memcmp_res f g n (mr !!! Regidx (mword_of_int 10 : mword 5))⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type MEMCMP.
  Parameter wp_memcmp_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq1 dq2 : dfrac) (b : bool) (p : mword 64),
      wp_memcmp_sconf_body mm n f g K dq1 dq2 b p.
End MEMCMP.

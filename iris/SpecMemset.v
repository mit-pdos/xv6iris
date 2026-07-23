(* SpecMemset.v -- the general whole-function spec of the kernel's
   [memset]: fill an ARBITRARY array of [len] bytes at base [p] with the low
   byte of [cval].  This is memset's actual contract; the page-level spec
   (SpecMemsetPage) and walk's page-zeroing step are both instances at
   len = 4096.  Stated over the per-byte buffer (not [page_own]), so it is
   independent of the kalloc page abstraction.

   Requires only the definitional layer -- never a whole-function proof file --
   so every function proof can be checked in parallel. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language lifting.
From iris.base_logic.lib Require Import ghost_var invariants gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes RiscvLang RiscvPtsto.
Require Import RegFile.
Require Import InstrBytes.
Require Import SmodeCore.
Require Import KernelText.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Import Defs.

Notation MS := KernelSyms.memset.

(* memset(p, cval, len): fills [len] bytes at base [p] with [cval]'s low byte.
   [len] need only fit in 32 bits (the C source truncates the count to
   [unsigned int] via a slli/srli round-trip); len = 0 is allowed (the source's
   [n == 0] test skips the loop) and so is an array that wraps the 64-bit
   address space -- the caller's buffer is indexed by [pa_add], which wraps
   exactly as the hardware's pointer increment does.  memset saves ra/s0 in a
   2-slot frame, so it needs 2 of the [n] available stack slots and returns
   them (avail [n] preserved). *)
Definition wp_memset_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memset in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p := m0 !!! Regidx a0_idx in
  let ret_tgt := ret_pc ra0 in
  let cbyte := nth_byte (autocast (T := mword) (subrange_vec_dec cval (Z.sub (Z.mul 1 8) 1) 0) : mword 8) 0 in
  (2 <= n)%nat ->
  (Z.of_nat len < 2 ^ 32)%Z ->
  m0 !!! Regidx a1_idx = cval ->
  m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64) ->
  sie_cap_gpr γ m0 n -∗
  kernel_text -∗ pc_is pcE -∗
  ([∗ list] j ∈ seq 0 len, (pa_add p j) ↦ₘ olds j) -∗
  ( ∀ mfin,
    sie_cap_gpr γ mfin n -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p j) ↦ₘ cbyte) -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MEMSET.
  Parameter wp_memset_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (len : nat) (cval : mword 64) (olds : nat -> bv 8),
      wp_memset_sconf_body γ Φ m0 n len cval olds.
End MEMSET.

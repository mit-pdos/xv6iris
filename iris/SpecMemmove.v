(* SpecMemmove.v -- the general whole-function spec of the kernel's [memmove]:
   copy [len] bytes from [p_src] to [p_dst].

   NON-OVERLAPPING ranges only, and that restriction is carried by SEPARATION,
   not by a pure side condition: the precondition owns the source bytes and the
   destination bytes as two separate conjuncts, which already says the two
   ranges are disjoint (a byte owned outright cannot also be owned as part of
   the other buffer).  The proof turns that ownership back into the pure
   non-aliasing fact where it is needed, so a caller never has to state an
   address-arithmetic disjointness hypothesis -- it just hands over the two
   buffers it owns.

   Why the restriction is the right contract: the source's overlap test is
   [src < dst && src + n > dst], and only its true branch runs the descending
   copy loop (memmove+0x3e..+0x5e).  Under the separated precondition that test
   can never be true, so the whole descending loop is unreachable and the spec
   is the plain forward copy.  Every xv6 kernel caller copies between distinct
   objects, so nothing needs the overlapping contract; a caller that did would
   need a genuinely different spec (a byte-list permutation over ONE buffer),
   not a weakening of this one.

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

(* memmove(dst, src, len): copies [len] bytes from [src] to [dst] and returns
   [dst] in a0.  As with memset, [len] need only fit in 32 bits (the C source
   truncates the count to [unsigned int] via an slli/srli round-trip), len = 0
   is allowed (the source's [n == 0] test skips the loop), and the buffers are
   indexed by [pa_add], which wraps the 64-bit address space exactly as the
   hardware's pointer increment does.  memmove saves ra/s0 in a 2-slot frame,
   so it needs 2 of the [n] available stack slots and returns them (avail [n]
   preserved). *)
Definition wp_memmove_sconf_body `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
    (γ : gname) (Φ : mval -> iProp Σ)
    (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memmove in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p_dst := m0 !!! Regidx a0_idx in
  let p_src := m0 !!! Regidx a1_idx in
  let ret_tgt := ret_pc ra0 in
  (2 <= n)%nat ->
  (Z.of_nat len < 2 ^ 32)%Z ->
  m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64) ->
  sie_cap_gpr γ m0 n -∗
  kernel_text -∗ pc_is pcE -∗
  ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ src_bytes j) -∗
  ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ dst_olds j) -∗
  ( ∀ mfin,
    sie_cap_gpr γ mfin n -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ src_bytes j) -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ src_bytes j) -∗
    ⌜ mfin !!! Regidx a0_idx = p_dst ⌝ -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type MEMMOVE.
  Parameter wp_memmove_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{CID : CpuId}
      (γ : gname) (Φ : mval -> iProp Σ)
      (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8),
      wp_memmove_sconf_body γ Φ m0 n len src_bytes dst_olds.
End MEMMOVE.

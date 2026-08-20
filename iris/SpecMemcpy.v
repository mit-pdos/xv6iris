(* SpecMemcpy.v -- the whole-function spec of the kernel's [memcpy].

   xv6's memcpy is a SHIM: twenty bytes that build a 2-slot ra/s0 frame,
   [jal ra,memmove] with a0/a1/a2 untouched, tear the frame down and return.
   It does not even move a0 into place -- memmove's return value (the
   destination pointer) is already in a0 when memcpy's [c.jr ra] runs.  So the
   contract IS memmove's contract restated at memcpy's entry point, and the
   proof consumes the MEMMOVE module type exactly as any other caller does.

   The one visible difference is the stack budget: memcpy spends 2 of the [n]
   available slots on its own frame and memmove then needs 2 more, so the
   precondition asks for [4 <= n] where SpecMemmove.v asks for [2 <= n].
   Everything else -- NON-OVERLAPPING ranges carried by separation rather than
   by a pure side condition, the [len < 2^32] truncation bound, the [pa_add]
   indexing that wraps exactly as the hardware's pointer increment does, and
   the [a0 = dst] / [callee_saved] postcondition -- is inherited verbatim; see
   SpecMemmove.v's header for why that is the right shape.

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
Require Import RegFile WpNext.
Require Import InstrBytes.
Require Import RiscvExtras.
Require Import KernelText.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.

(* THE TWO BUFFERS CARRY THEIR OWN TIERS.  [kts] is the SOURCE's, [ktw] the
   DESTINATION's, each below the accessing hart's regime [kt] -- the same
   two-tier shape [WpSconfMem]'s merged leaves have, and it is FORCED: copyin
   moves a KT0 page window into the caller's frame buffer (which rides [kt]),
   copyout moves the other way, and either_copy's kernel arm has both at
   [kt].  One shared datum tier cannot state any of those.  Both tiers are
   EXPLICIT: eager [KtierLe] refl would otherwise silently re-derive them as
   [kt] and every page caller would fail at its give-back. *) 
Definition wp_memcpy_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
    (kt kts ktw : ktier) `{!KtierLe kts kt} `{!KtierLe ktw kt}
    (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8) (b : bool) (p : mword 64) :=
  let a0_idx : mword 5 := mword_of_int 10 in
  let a1_idx : mword 5 := mword_of_int 11 in
  let a2_idx : mword 5 := mword_of_int 12 in
  let pcE := mword_of_int KernelSyms.memcpy in
  let ra0 := m0 !!! Regidx (mword_of_int 1 : mword 5) in
  let p_dst := m0 !!! Regidx a0_idx in
  let p_src := m0 !!! Regidx a1_idx in
  let ret_tgt := ret_pc ra0 in
  (4 <= n)%nat ->
  (Z.of_nat len < 2 ^ 32)%Z ->
  m0 !!! Regidx a2_idx = (mword_of_int (Z.of_nat len) : mword 64) ->
  sie_cap_gpr kt m0 n b p -∗
  kernel_text -∗ pc_is pcE -∗
  ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ[kts] src_bytes j) -∗
  ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ[ktw] dst_olds j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mfin,
    sie_cap_gpr kt mfin n b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_src j) ↦ₘ[kts] src_bytes j) -∗
    ([∗ list] j ∈ seq 0 len, (pa_add p_dst j) ↦ₘ[ktw] src_bytes j) -∗
    ⌜ mfin !!! Regidx a0_idx = p_dst ⌝ -∗
    ⌜ callee_saved m0 mfin ⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type MEMCPY.
  Parameter wp_memcpy_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId}
      (kt kts ktw : ktier) `{!KtierLe kts kt} `{!KtierLe ktw kt}
      (m0 : regfile) (n : nat) (len : nat) (src_bytes dst_olds : nat -> bv 8) (b : bool) (p : mword 64),
      wp_memcpy_sconf_body kt kts ktw m0 n len src_bytes dst_olds b p.
End MEMCPY.

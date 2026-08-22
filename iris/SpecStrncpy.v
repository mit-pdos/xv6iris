(* Public contract for xv6's [strncpy].  Unlike [safestrcpy], this is the
   ISO-C bounded copy: it copies through the first source NUL when one occurs
   in the first [n] bytes, then writes NUL into every remaining destination
   byte.  If there is no such NUL, all [n] bytes are copied and no terminator
   is invented. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import gen_heap invariants ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import RiscvModelBytes RiscvPtsto RiscvLang.
Require Import InstrBytes KernelText.
Require Import RegFile.
Require Import RiscvExtras.
Require Import CalleeSaved.
Require Import IntrDefs WpNext.
Require Import ByteBuf.
From Kernel Require KernelSyms.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Import Defs.
Local Open Scope Z_scope.

(* [snc_post f h n] describes the final [n]-byte destination.  The first arm
   is the full-copy case.  The second records the first source NUL and the
   zero-filled suffix (including the copied NUL itself). *)
Definition snc_post (f h : nat -> bv 8) (n : nat) : Prop :=
  (bb_nonul f n /\ forall j, (j < n)%nat -> h j = f j) \/
  exists k, (k < n)%nat /\ bb_cstr f k /\
    (forall j, (j < k)%nat -> h j = f j) /\
    (forall j, (k <= j)%nat -> (j < n)%nat -> h j = (mword_of_int 0 : mword 8)).

Definition wp_strncpy_sconf_body `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
    (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.strncpy in
  let s := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let t := mm !!! Regidx (mword_of_int 11 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (2 <= K)%nat ->
  mm !!! Regidx (mword_of_int 12 : mword 5) = (mword_of_int (Z.of_nat n) : mword 64) ->
  (Z.of_nat n < 2 ^ 31)%Z ->
  sie_cap_gpr KT1 mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] g j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ (mr : regfile) (h : nat -> bv 8),
    sie_cap_gpr KT1 mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 n, (pa_add t j) ↦ₘ[KT1]{dq} f j) -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ[KT1] h j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜mr !!! Regidx (mword_of_int 10 : mword 5) = s⌝ -∗
    ⌜(n = 0%nat /\ h = g) \/ (0 < n)%nat /\ snc_post f h n⌝ -∗
    WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type STRNCPY.
  Parameter wp_strncpy_sconf :
    forall `{!riscvGS Σ, !xv6G Σ} `{GEN : GenId} `{CID : CpuId} (mm : regfile)
      (n : nat) (f g : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_strncpy_sconf_body mm n f g K dq b p.
End STRNCPY.

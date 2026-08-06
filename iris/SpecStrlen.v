(* SpecStrlen.v -- the public interface of strlen(), stated independently of
   its proof.

     int strlen(const char *s) { int n; for (n = 0; s[n]; n++) ; return n; }

   @ KernelSyms.strlen = 0x80000e52, 44 bytes; a 2-slot frame, no callees.

   THE CONTRACT is the exact dual of copyinstr's postcondition, and stated in
   the same vocabulary so that the two compose with nothing in between (which
   is what fetchstr does): the caller owns [n] consecutive bytes named by [f],
   and [ByteBuf.bb_cstr f k] says the NUL sits at index [k] and nowhere before
   it.  strlen then returns [k].

   Three deliberate choices:

   - THE BUFFER MAY BE LONGER THAN THE STRING ([k < n], not [n = k+1]).
     strlen reads only bytes [0 .. k], so the extra bytes are not needed;
     taking them anyway is what lets a caller that holds a fixed-size buffer
     -- fetchstr's [char *buf] of [max] bytes -- pass it whole, with no split
     and rejoin around the call.  A caller who owns exactly the string picks
     [n = S k].
   - dfrac-GENERIC.  strlen writes nothing, so it takes the bytes at any
     [dq] and hands them back unchanged; a read-only image string
     ([DfracDiscarded]) works as well as an owned buffer.
   - [k < 2^31] IS A PREMISE, because the return is a C [int]: the machine
     computes the length with a [subw] (a 32-bit subtract of the two cursors,
     sign-extended), so the answer is [k] only while [k] fits in an [int].
     A caller with a fixed-size buffer discharges it from [n]. *)
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
Require Import ByteBuf.
From Kernel Require KernelSyms.
Import Defs.
Local Open Scope Z_scope.


Definition wp_strlen_sconf_body `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
    (Φ : mval -> iProp Σ) (mm : regfile)
    (n k : nat) (f : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64) :=
  let pcE : mword 64 := mword_of_int KernelSyms.strlen in
  let s := mm !!! Regidx (mword_of_int 10 : mword 5) in
  let ret_tgt := ret_pc (mm !!! Regidx (mword_of_int 1 : mword 5)) in
  (* the 2-slot frame; strlen calls nothing *)
  (2 <= K)%nat ->
  (k < n)%nat ->
  bb_cstr f k ->
  (Z.of_nat k < 2 ^ 31)%Z ->
  sie_cap_gpr mm K b p -∗
  kernel_text -∗
  pc_is pcE -∗
  ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ{dq} f j) -∗
  wp_next b p (fun (CID : CpuId) =>
    ∀ mr : regfile,
    sie_cap_gpr mr K b p -∗
    pc_is ret_tgt -∗
    ([∗ list] j ∈ seq 0 n, (pa_add s j) ↦ₘ{dq} f j) -∗
    ⌜callee_saved mm mr⌝ -∗
    ⌜mr !!! Regidx (mword_of_int 10 : mword 5)
       = (mword_of_int (Z.of_nat k) : mword 64)⌝ -∗
    WP (Loop : expr riscv_lang) {{ Φ }}) -∗
  WP (Loop : expr riscv_lang) {{ Φ }}.

Module Type STRLEN.
  Parameter wp_strlen_sconf :
    forall `{!riscvGS Σ, !sieG Σ} `{GEN : GenId} `{CID : CpuId}
      (Φ : mval -> iProp Σ) (mm : regfile)
      (n k : nat) (f : nat -> bv 8) (K : nat) (dq : dfrac) (b : bool) (p : mword 64),
      wp_strlen_sconf_body Φ mm n k f K dq b p.
End STRLEN.
